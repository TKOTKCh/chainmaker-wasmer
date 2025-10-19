//! `metering` is a middleware for tracking how many operators are
//! executed in total and putting a limit on the total number of
//! operators executed. The WebAssembly instance execution is stopped
//! when the limit is reached.
//!
//! # Example
//!
//! [See the `metering` detailed and complete
//! example](https://github.com/wasmerio/wasmer/blob/main/examples/metering.rs).
use regex::Regex; // 需要引入 regex 库
use std::collections::HashSet;
use std::convert::TryInto;
use std::fmt;
use std::fmt::Debug;
use std::sync::{Arc, Mutex};
use wasmer::wasmparser::{BlockType as WpTypeOrFuncType, Operator};
use wasmer::{
    sys::{FunctionMiddleware, MiddlewareError, MiddlewareReaderState, ModuleMiddleware},
    AsStoreMut, ExportIndex, GlobalInit, GlobalType, Instance, LocalFunctionIndex, Mutability,
    Type,
};
use wasmer_types::{GlobalIndex, ModuleInfo,FunctionIndex};


#[derive(Clone)]
struct MeteringGlobalIndexes(GlobalIndex, GlobalIndex);

impl MeteringGlobalIndexes {
    /// The global index in the current module for remaining points.
    fn remaining_points(&self) -> GlobalIndex {
        self.0
    }

    /// The global index in the current module for a boolean indicating whether points are exhausted
    /// or not.
    /// This boolean is represented as a i32 global:
    ///   * 0: there are remaining points
    ///   * 1: points have been exhausted
    fn points_exhausted(&self) -> GlobalIndex {
        self.1
    }
}

impl fmt::Debug for MeteringGlobalIndexes {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("MeteringGlobalIndexes")
            .field("remaining_points", &self.remaining_points())
            .field("points_exhausted", &self.points_exhausted())
            .finish()
    }
}

/// ✅ Go 版本的 Metering，中途跳过 runtime 函数
pub struct ChainMakerMetering<F: Fn(&Operator) -> u64 + Send + Sync> {
    initial_limit: u64,
    cost_function: Arc<F>,
    global_indexes: Mutex<Option<MeteringGlobalIndexes>>,
    runtime_funcs: Mutex<HashSet<String>>, // 存储 runtime 函数索引
    func_names: Mutex<Vec<String>>, // ✅ 新增：保存所有函数名
    func_name_match: Option<String>,
}

/// The module-level metering middleware.
///
/// # Panic
///
/// An instance of `Metering` should _not_ be shared among different
/// modules, since it tracks module-specific information like the
/// global index to store metering state. Attempts to use a `Metering`
/// instance from multiple modules will result in a panic.
///
/// # Example
///
/// ```rust
/// use std::sync::Arc;
/// use wasmer::{wasmparser::Operator, sys::CompilerConfig};
/// use wasmer_middlewares::Metering;
///
/// fn create_metering_middleware(compiler_config: &mut dyn CompilerConfig) {
///     // Let's define a dummy cost function,
///     // which counts 1 for all operators.
///     let cost_function = |_operator: &Operator| -> u64 { 1 };
///
///     // Let's define the initial limit.
///     let initial_limit = 10;
///
///     // Let's creating the metering middleware.
///     let metering = Arc::new(Metering::new(
///         initial_limit,
///         cost_function
///     ));
///
///     // Finally, let's push the middleware.
///     compiler_config.push_middleware(metering);
/// }
/// ```
pub struct Metering<F: Fn(&Operator) -> u64 + Send + Sync> {
    /// Initial limit of points.
    initial_limit: u64,

    /// Function that maps each operator to a cost in "points".
    cost_function: Arc<F>,

    /// The global indexes for metering points.
    global_indexes: Mutex<Option<MeteringGlobalIndexes>>,
}

/// The function-level metering middleware.
pub struct FunctionMetering<F: Fn(&Operator) -> u64 + Send + Sync> {
    /// Function that maps each operator to a cost in "points".
    cost_function: Arc<F>,

    /// The global indexes for metering points.
    global_indexes: MeteringGlobalIndexes,

    /// Accumulated cost of the current basic block.
    accumulated_cost: u64,

    skip: bool, // 是否跳过常规metering 按指令计费

    name: String
}

/// Represents the type of the metering points, either `Remaining` or
/// `Exhausted`.
///
/// # Example
///
/// See the [`get_remaining_points`] function to get an example.
#[derive(Debug, Eq, PartialEq)]
pub enum MeteringPoints {
    /// The given number of metering points is left for the execution.
    /// If the value is 0, all points are consumed but the execution
    /// was not terminated.
    Remaining(u64),

    /// The execution was terminated because the metering points were
    /// exhausted.  You can recover from this state by setting the
    /// points via [`set_remaining_points`] and restart the execution.
    Exhausted,
}

impl<F: Fn(&Operator) -> u64 + Send + Sync> Metering<F> {
    /// Creates a `Metering` middleware.
    ///
    /// When providing a cost function, you should consider that branching operations do
    /// additional work to track the metering points and probably need to have a higher cost.
    /// To find out which operations are affected by this, you can call [`is_accounting`].
    pub fn new(initial_limit: u64, cost_function: F) -> Self {
        Self {
            initial_limit,
            cost_function: Arc::new(cost_function),
            global_indexes: Mutex::new(None),
        }
    }
}

impl<F: Fn(&Operator) -> u64 + Send + Sync> ChainMakerMetering<F> {
    pub fn new(initial_limit: u64, cost_function: F,function_match: Option<String>) -> Self {
        let func_name_match = function_match.map(|s| s.to_string()); // 转为 Option<String>

        Self {
            initial_limit,
            cost_function: Arc::new(cost_function),
            global_indexes: Mutex::new(None),
            runtime_funcs: Mutex::new(HashSet::new()),
            func_names: Mutex::new(vec![]),
            func_name_match, // 存储 Option<String>
        }
    }
}

impl<F: Fn(&Operator) -> u64 + Send + Sync> fmt::Debug for Metering<F> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Metering")
            .field("initial_limit", &self.initial_limit)
            .field("cost_function", &"<function>")
            .field("global_indexes", &self.global_indexes)
            .finish()
    }
}

impl<F: Fn(&Operator) -> u64 + Send + Sync> fmt::Debug for ChainMakerMetering<F> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("ChainMakerMetering")
            .field("initial_limit", &self.initial_limit)
            .field("cost_function", &"<function>")
            .finish()
    }
}

fn strip_last_suffix(name: &str) -> &str {
    if let Some(pos) = name.rfind('_') {
        &name[..pos]  // 截取从开始到最后一个 '_' 的前面部分
    } else {
        name
    }
}
fn is_go_compiler_func(name: &str) -> bool {
    const GO_RUNTIME_PREFIXES: &[&str] = &[
        "runtime", "internal", "reflect",
        "sync", "type", "itab",
        "go.func.", "go.string.", "gcWriteBarrier","io",
        "memmove", "memclrNoHeapPointers","go_"
    ];

    GO_RUNTIME_PREFIXES.iter().any(|p| name.contains(p))
}

fn is_user_code(name: &str, func_name_match: Option<&String>) -> bool {
    let name_lower = name.to_lowercase();
    //先判断是否是go编译器的runtime相关的函数
    if is_go_compiler_func(&name_lower) {
        return false
    }
    // 如果 func_name_match 存在且非空，尝试编译为正则表达式并匹配
    let custom_match = func_name_match
        .filter(|pattern| !pattern.is_empty())
        .and_then(|pattern| Regex::new(pattern).ok()) // 编译正则表达式（忽略错误）
        .map_or(false, |regex| regex.is_match(&name_lower)); // 正则匹配

    // 如果 custom_match 为 true，直接返回 true；否则检查固定规则
    custom_match || {
        name.starts_with("main.")
            ||name.starts_with("json")
            ||name.starts_with("math")
            ||name.starts_with("strings")
            ||name.starts_with("encoding")
            ||name.starts_with("time")
            ||name.starts_with("fmt")
            || name_lower.contains("chainmaker")
            || name_lower.contains("sdk")
            || name.is_empty()
    }
}

use std::collections::HashMap;
use std::ffi::CStr;
use std::os::raw::c_char;
use lazy_static::lazy_static;

lazy_static! {
    static ref FUNCTION_VALUE_MAP: HashMap<&'static str, u64> = {
        let mut map = HashMap::new();
        // map.insert("strconv.ParseInt", 726);
        // map.insert("encoding_json.Marshal", 504903);
        // map.insert("encoding_json.Unmarshal", 1208204);
        map
    };
}

fn get_fixed_value(name: &str) -> Option<u64> {
    FUNCTION_VALUE_MAP.get(name).copied()
}
impl<F: Fn(&Operator) -> u64 + Send + Sync + 'static> ModuleMiddleware for ChainMakerMetering<F> {
    /// Generates a `FunctionMiddleware` for a given function.
    fn generate_function_middleware(&self, func_idx: LocalFunctionIndex) -> Box<dyn FunctionMiddleware> {
        let func_names = self.func_names.lock().unwrap();
        let idx = func_idx.as_u32() as usize;
        let name = func_names.get(idx).cloned().unwrap_or_default();
        let skip = !is_user_code(&name,self.func_name_match.as_ref());
        // let skip=is_go_compiler_func(&name);
        // println!(
        //     "skip:{} mapped_name='{}' func_idx={} {}",
        //     skip,
        //     name,
        //     func_idx.as_u32(),
        //     match get_fixed_value(&name) {
        //         Some(value) => format!("preset_value={}", value),
        //         None => "no_preset".to_string(),
        //     }
        // );
        Box::new(FunctionMetering {
            cost_function: self.cost_function.clone(),
            global_indexes: self.global_indexes.lock().unwrap().clone().unwrap(),
            accumulated_cost: 0,
            skip,
            name,
        })
    }

    /// Transforms a `ModuleInfo` struct in-place. This is called before application on functions begins.
    fn transform_module_info(&self, module_info: &mut ModuleInfo) -> Result<(), MiddlewareError> {
        let mut global_indexes = self.global_indexes.lock().unwrap();

        if global_indexes.is_some() {
            panic!("Metering::transform_module_info: Attempting to use a `Metering` middleware from multiple modules.");
        }

        // 1. 扫描并获取函数名
        // chenhang 特别注意LocalFunctionIndex和wasm解析出来的FunctionIndex不一定一致！！！二者中间差着imported_functions
        // generate_function_middleware里面传过来的是LocalFunctionIndex
        let mut func_names = self.func_names.lock().unwrap();
        func_names.clear();
        func_names.resize(module_info.functions.len(), String::new());
        for (idx, name) in module_info.function_names.iter() {
            // 获取 Option<LocalFunctionIndex>
            let local_function_index = module_info.local_func_index(*idx);
            if let Some(local_idx) = local_function_index {
                // 直接访问元组结构体的内部字段 `.0`，并转换为 usize
                let local_idx_usize = local_idx.as_u32() as usize;
                if local_idx_usize < func_names.len() {
                    // println!(
                    //     "module function '{}' local_function_index '{}'",
                    //     name, local_idx_usize
                    // );
                    func_names[local_idx_usize] = name.clone();
                }
            } else {
                // 如果 local_function_index 是 None，说明是 imported function，可以打印警告或跳过
                println!("Warning: Function '{}' is an imported function (no local index)", name);
            }
        }

        if func_names.is_empty() {
            // 如果没有调试信息，填充空字符串占位
            func_names.resize(module_info.functions.len(), String::new());
        }

        // //TODO chenhang:是否真的需要runtime_funcs?感觉可以删除
        let mut runtime_funcs = self.runtime_funcs.lock().unwrap();
        for (name, export) in module_info.exports.iter() {
            if let ExportIndex::Function(_) = export {
                // println!("Exporting function '{}'", name);
            }
        }

        // Append a global for remaining points and initialize it.
        let remaining_points_global_index = module_info
            .globals
            .push(GlobalType::new(Type::I64, Mutability::Var));


        module_info
            .global_initializers
            .push(GlobalInit::I64Const(self.initial_limit as i64));

        module_info.exports.insert(
            "wasmer_metering_remaining_points".to_string(),
            ExportIndex::Global(remaining_points_global_index),
        );

        // Append a global for the exhausted points boolean and initialize it.
        let points_exhausted_global_index = module_info
            .globals
            .push(GlobalType::new(Type::I32, Mutability::Var));

        module_info
            .global_initializers
            .push(GlobalInit::I32Const(0));

        module_info.exports.insert(
            "wasmer_metering_points_exhausted".to_string(),
            ExportIndex::Global(points_exhausted_global_index),
        );

        *global_indexes = Some(MeteringGlobalIndexes(
            remaining_points_global_index,
            points_exhausted_global_index,
        ));

        Ok(())
    }
}

impl<F: Fn(&Operator) -> u64 + Send + Sync + 'static> ModuleMiddleware for Metering<F> {
    /// Generates a `FunctionMiddleware` for a given function.
    fn generate_function_middleware(&self, _: LocalFunctionIndex) -> Box<dyn FunctionMiddleware> {
        Box::new(FunctionMetering {
            cost_function: self.cost_function.clone(),
            global_indexes: self.global_indexes.lock().unwrap().clone().unwrap(),
            accumulated_cost: 0,
            skip: false,
            name: "".to_string(),
        })
    }

    /// Transforms a `ModuleInfo` struct in-place. This is called before application on functions begins.
    fn transform_module_info(&self, module_info: &mut ModuleInfo) -> Result<(), MiddlewareError> {
        let mut global_indexes = self.global_indexes.lock().unwrap();

        if global_indexes.is_some() {
            panic!("Metering::transform_module_info: Attempting to use a `Metering` middleware from multiple modules.");
        }

        // Append a global for remaining points and initialize it.
        let remaining_points_global_index = module_info
            .globals
            .push(GlobalType::new(Type::I64, Mutability::Var));

        module_info
            .global_initializers
            .push(GlobalInit::I64Const(self.initial_limit as i64));

        module_info.exports.insert(
            "wasmer_metering_remaining_points".to_string(),
            ExportIndex::Global(remaining_points_global_index),
        );

        // Append a global for the exhausted points boolean and initialize it.
        let points_exhausted_global_index = module_info
            .globals
            .push(GlobalType::new(Type::I32, Mutability::Var));

        module_info
            .global_initializers
            .push(GlobalInit::I32Const(0));

        module_info.exports.insert(
            "wasmer_metering_points_exhausted".to_string(),
            ExportIndex::Global(points_exhausted_global_index),
        );

        *global_indexes = Some(MeteringGlobalIndexes(
            remaining_points_global_index,
            points_exhausted_global_index,
        ));

        Ok(())
    }
}

/// Returns `true` if and only if the given operator is an accounting operator.
/// Accounting operators do additional work to track the metering points.
pub fn is_accounting(operator: &Operator) -> bool {
    // Possible sources and targets of a branch.
    matches!(
        operator,
        Operator::Loop { .. } // loop headers are branch targets
            | Operator::End // block ends are branch targets
            | Operator::If { .. } // branch source, "if" can branch to else branch
            | Operator::Else // "else" is the "end" of an if branch
            | Operator::Br { .. } // branch source
            | Operator::BrTable { .. } // branch source
            | Operator::BrIf { .. } // branch source
            | Operator::Call { .. } // function call - branch source
            | Operator::CallIndirect { .. } // function call - branch source
            | Operator::Return // end of function - branch source
            // exceptions proposal
            | Operator::Throw { .. } // branch source
            | Operator::ThrowRef // branch source
            | Operator::Rethrow { .. } // branch source
            | Operator::Delegate { .. } // branch source
            | Operator::Catch { .. } // branch target
            // tail_call proposal
            | Operator::ReturnCall { .. } // branch source
            | Operator::ReturnCallIndirect { .. } // branch source
            // gc proposal
            | Operator::BrOnCast { .. } // branch source
            | Operator::BrOnCastFail { .. } // branch source
            // function_references proposal
            | Operator::CallRef { .. } // branch source
            | Operator::ReturnCallRef { .. } // branch source
            | Operator::BrOnNull { .. } // branch source
            | Operator::BrOnNonNull { .. } // branch source
    )
}

impl<F: Fn(&Operator) -> u64 + Send + Sync> fmt::Debug for FunctionMetering<F> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("FunctionMetering")
            .field("cost_function", &"<function>")
            .field("global_indexes", &self.global_indexes)
            .finish()
    }
}
lazy_static! {
    static ref SEEN_FUNCTIONS: Mutex<HashMap<String, bool>> = Mutex::new(HashMap::new());
}

// if self.name.to_lowercase().contains("normalCal"){
//     println!("normalCal: {}",self.accumulated_cost);
// }
// 输出

impl<F: Fn(&Operator) -> u64 + Send + Sync> FunctionMiddleware for FunctionMetering<F> {
    fn feed<'a>(
        &mut self,
        operator: Operator<'a>,
        state: &mut MiddlewareReaderState<'a>,
    ) -> Result<(), MiddlewareError> {
        // let mut seen_functions = SEEN_FUNCTIONS.lock().unwrap();
        // if !seen_functions.contains_key(&self.name) {
        //     // println!("FunctionMetering: {} skip:{}", self.name,self.skip);
        //     seen_functions.insert(self.name.clone(), true);
        // }
        // 跳过带skip标签函数的
        if self.skip {
            self.accumulated_cost = get_fixed_value(&self.name).unwrap_or(0);
            state.push_operator(operator);
            return Ok(());
        }
        // Get the cost of the current operator, and add it to the accumulator.
        // This needs to be done before the metering logic, to prevent operators like `Call` from escaping metering in some
        // corner cases.
        // println!("{:?}", operator);
        self.accumulated_cost += (self.cost_function)(&operator);

        // Finalize the cost of the previous basic block and perform necessary checks.
        if is_accounting(&operator) && self.accumulated_cost > 0 {
            state.extend(&[
                // if unsigned(globals[remaining_points_index]) < unsigned(self.accumulated_cost) { throw(); }
                Operator::GlobalGet {
                    global_index: self.global_indexes.remaining_points().as_u32(),
                },
                Operator::I64Const {
                    value: self.accumulated_cost as i64,
                },
                Operator::I64LtU,
                Operator::If {
                    blockty: WpTypeOrFuncType::Empty,
                },
                Operator::I32Const { value: 1 },
                Operator::GlobalSet {
                    global_index: self.global_indexes.points_exhausted().as_u32(),
                },
                Operator::Unreachable,
                Operator::End,
                // globals[remaining_points_index] -= self.accumulated_cost;
                Operator::GlobalGet {
                    global_index: self.global_indexes.remaining_points().as_u32(),
                },
                Operator::I64Const {
                    value: self.accumulated_cost as i64,
                },
                Operator::I64Sub,
                Operator::GlobalSet {
                    global_index: self.global_indexes.remaining_points().as_u32(),
                },
            ]);

            self.accumulated_cost = 0;
        }
        state.push_operator(operator);

        Ok(())
    }
}

/// Get the remaining points in an [`Instance`][wasmer::Instance].
///
/// Note: This can be used in a headless engine after an ahead-of-time
/// compilation as all required state lives in the instance.
///
/// # Panic
///
/// The [`Instance`][wasmer::Instance) must have been processed with
/// the [`Metering`] middleware at compile time, otherwise this will
/// panic.
///
/// # Example
///
/// ```rust
/// use wasmer::Instance;
/// use wasmer::AsStoreMut;
/// use wasmer_middlewares::metering::{get_remaining_points, MeteringPoints};
///
/// /// Check whether the instance can continue to run based on the
/// /// number of remaining points.
/// fn can_continue_to_run(store: &mut impl AsStoreMut, instance: &Instance) -> bool {
///     matches!(get_remaining_points(store, instance), MeteringPoints::Remaining(points) if points > 0)
/// }
/// ```
pub fn get_remaining_points(ctx: &mut impl AsStoreMut, instance: &Instance) -> MeteringPoints {
    let exhausted: i32 = instance
        .exports
        .get_global("wasmer_metering_points_exhausted")
        .expect("Can't get `wasmer_metering_points_exhausted` from Instance")
        .get(ctx)
        .try_into()
        .expect("`wasmer_metering_points_exhausted` from Instance has wrong type");

    if exhausted > 0 {
        return MeteringPoints::Exhausted;
    }

    let points = instance
        .exports
        .get_global("wasmer_metering_remaining_points")
        .expect("Can't get `wasmer_metering_remaining_points` from Instance")
        .get(ctx)
        .try_into()
        .expect("`wasmer_metering_remaining_points` from Instance has wrong type");

    MeteringPoints::Remaining(points)
}

/// Set the new provided remaining points in an
/// [`Instance`][wasmer::Instance].
///
/// Note: This can be used in a headless engine after an ahead-of-time
/// compilation as all required state lives in the instance.
///
/// # Panic
///
/// The given [`Instance`][wasmer::Instance] must have been processed
/// with the [`Metering`] middleware at compile time, otherwise this
/// will panic.
///
/// # Example
///
/// ```rust
/// use wasmer::{AsStoreMut, Instance};
/// use wasmer_middlewares::metering::set_remaining_points;
///
/// fn update_remaining_points(store: &mut impl AsStoreMut, instance: &Instance) {
///     // The new limit.
///     let new_limit = 10;
///
///     // Update the remaining points to the `new_limit`.
///     set_remaining_points(store, instance, new_limit);
/// }
/// ```
pub fn set_remaining_points(ctx: &mut impl AsStoreMut, instance: &Instance, points: u64) {
    instance
        .exports
        .get_global("wasmer_metering_remaining_points")
        .expect("Can't get `wasmer_metering_remaining_points` from Instance")
        .set(ctx, points.into())
        .expect("Can't set `wasmer_metering_remaining_points` in Instance");

    instance
        .exports
        .get_global("wasmer_metering_points_exhausted")
        .expect("Can't get `wasmer_metering_points_exhausted` from Instance")
        .set(ctx, 0i32.into())
        .expect("Can't set `wasmer_metering_points_exhausted` in Instance");
}

#[cfg(test)]
mod tests {
    use super::*;

    use std::sync::Arc;
    use wasmer::sys::EngineBuilder;
    use wasmer::{
        imports,
        sys::{CompilerConfig, Cranelift},
        wat2wasm, Module, Store, TypedFunction,
    };

    fn cost_function(operator: &Operator) -> u64 {
        match operator {
            Operator::LocalGet { .. } | Operator::I32Const { .. } => 1,
            Operator::I32Add { .. } => 2,
            _ => 0,
        }
    }

    fn bytecode() -> Vec<u8> {
        wat2wasm(
            br#"(module
            (type $add_t (func (param i32) (result i32)))
            (func $add_one_f (type $add_t) (param $value i32) (result i32)
                local.get $value
                i32.const 1
                i32.add)
            (func $short_loop_f
                (local $x f64) (local $j i32)
                (local.set $x (f64.const 5.5))

                (loop $named_loop
                    ;; $j++
                    local.get $j
                    i32.const 1
                    i32.add
                    local.set $j

                    ;; if $j < 5, one more time
                    local.get $j
                    i32.const 5
                    i32.lt_s
                    br_if $named_loop
                )
            )
            (func $infi_loop_f
                (loop $infi_loop_start
                    br $infi_loop_start
                )
            )
            (export "add_one" (func $add_one_f))
            (export "short_loop" (func $short_loop_f))
            (export "infi_loop" (func $infi_loop_f))
        )"#,
        )
            .unwrap()
            .into()
    }

    #[test]
    fn get_remaining_points_works() {
        let metering = Arc::new(Metering::new(10, cost_function));
        let mut compiler_config = Cranelift::default();
        compiler_config.push_middleware(metering);
        let mut store = Store::new(EngineBuilder::new(compiler_config));
        let module = Module::new(&store, bytecode()).unwrap();

        // Instantiate
        let instance = Instance::new(&mut store, &module, &imports! {}).unwrap();
        assert_eq!(
            get_remaining_points(&mut store, &instance),
            MeteringPoints::Remaining(10)
        );

        // First call
        //
        // Calling add_one costs 4 points. Here are the details of how it has been computed:
        // * `local.get $value` is a `Operator::LocalGet` which costs 1 point;
        // * `i32.const` is a `Operator::I32Const` which costs 1 point;
        // * `i32.add` is a `Operator::I32Add` which costs 2 points.
        let add_one: TypedFunction<i32, i32> = instance
            .exports
            .get_function("add_one")
            .unwrap()
            .typed(&store)
            .unwrap();
        add_one.call(&mut store, 1).unwrap();
        assert_eq!(
            get_remaining_points(&mut store, &instance),
            MeteringPoints::Remaining(6)
        );

        // Second call
        add_one.call(&mut store, 1).unwrap();
        assert_eq!(
            get_remaining_points(&mut store, &instance),
            MeteringPoints::Remaining(2)
        );

        // Third call fails due to limit
        assert!(add_one.call(&mut store, 1).is_err());
        assert_eq!(
            get_remaining_points(&mut store, &instance),
            MeteringPoints::Exhausted
        );
    }

    #[test]
    fn set_remaining_points_works() {
        let metering = Arc::new(Metering::new(10, cost_function));
        let mut compiler_config = Cranelift::default();
        compiler_config.push_middleware(metering);
        let mut store = Store::new(EngineBuilder::new(compiler_config));
        let module = Module::new(&store, bytecode()).unwrap();

        // Instantiate
        let instance = Instance::new(&mut store, &module, &imports! {}).unwrap();
        assert_eq!(
            get_remaining_points(&mut store, &instance),
            MeteringPoints::Remaining(10)
        );
        let add_one: TypedFunction<i32, i32> = instance
            .exports
            .get_function("add_one")
            .unwrap()
            .typed(&store)
            .unwrap();

        // Increase a bit to have enough for 3 calls
        set_remaining_points(&mut store, &instance, 12);

        // Ensure we can use the new points now
        add_one.call(&mut store, 1).unwrap();
        assert_eq!(
            get_remaining_points(&mut store, &instance),
            MeteringPoints::Remaining(8)
        );

        add_one.call(&mut store, 1).unwrap();
        assert_eq!(
            get_remaining_points(&mut store, &instance),
            MeteringPoints::Remaining(4)
        );

        add_one.call(&mut store, 1).unwrap();
        assert_eq!(
            get_remaining_points(&mut store, &instance),
            MeteringPoints::Remaining(0)
        );

        assert!(add_one.call(&mut store, 1).is_err());
        assert_eq!(
            get_remaining_points(&mut store, &instance),
            MeteringPoints::Exhausted
        );

        // Add some points for another call
        set_remaining_points(&mut store, &instance, 4);
        assert_eq!(
            get_remaining_points(&mut store, &instance),
            MeteringPoints::Remaining(4)
        );
    }

    #[test]
    fn metering_works_for_loops() {
        const INITIAL_POINTS: u64 = 10_000;

        fn cost(operator: &Operator) -> u64 {
            match operator {
                Operator::Loop { .. } => 1000,
                Operator::Br { .. } | Operator::BrIf { .. } => 10,
                Operator::F64Const { .. } => 7,
                _ => 0,
            }
        }

        // Short loop

        let metering = Arc::new(Metering::new(INITIAL_POINTS, cost));
        let mut compiler_config = Cranelift::default();
        compiler_config.push_middleware(metering);
        let mut store = Store::new(EngineBuilder::new(compiler_config));
        let module = Module::new(&store, bytecode()).unwrap();

        let instance = Instance::new(&mut store, &module, &imports! {}).unwrap();
        let short_loop: TypedFunction<(), ()> = instance
            .exports
            .get_function("short_loop")
            .unwrap()
            .typed(&store)
            .unwrap();
        short_loop.call(&mut store).unwrap();

        let points_used: u64 = match get_remaining_points(&mut store, &instance) {
            MeteringPoints::Exhausted => panic!("Unexpected exhausted"),
            MeteringPoints::Remaining(remaining) => INITIAL_POINTS - remaining,
        };

        assert_eq!(
            points_used,
            7 /* pre-loop instructions */ +
                1000 /* loop instruction */ + 50 /* five conditional breaks */
        );

        // Infinite loop

        let metering = Arc::new(Metering::new(INITIAL_POINTS, cost));
        let mut compiler_config = Cranelift::default();
        compiler_config.push_middleware(metering);
        let mut store = Store::new(EngineBuilder::new(compiler_config));
        let module = Module::new(&store, bytecode()).unwrap();

        let instance = Instance::new(&mut store, &module, &imports! {}).unwrap();
        let infi_loop: TypedFunction<(), ()> = instance
            .exports
            .get_function("infi_loop")
            .unwrap()
            .typed(&store)
            .unwrap();
        infi_loop.call(&mut store).unwrap_err(); // exhausted leads to runtime error

        assert_eq!(
            get_remaining_points(&mut store, &instance),
            MeteringPoints::Exhausted
        );
    }
}