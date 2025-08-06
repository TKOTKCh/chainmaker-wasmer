use sha2::{Sha256, Digest};
use anyhow::Result;
use num_bigint::BigInt;
use num_traits::ToPrimitive;
use wasmer_types::ImportError;
use crate::{error::InstantiationError, exports::Exports, imports::Imports, macros::backend::gen_rt_ty, module::Module, store::AsStoreMut, AsStoreRef, Extern, Function, FunctionEnv, FunctionEnvMut, Global, LinkError, Memory, MemoryView, RuntimeError, WasmPtr};

/// A WebAssembly Instance is a stateful, executable
/// instance of a WebAssembly [`Module`].
///
/// Instance objects contain all the exported WebAssembly
/// functions, memories, tables and globals that allow
/// interacting with WebAssembly.
///
/// Spec: <https://webassembly.github.io/spec/core/exec/runtime.html#module-instances>
#[derive(Clone, PartialEq, Eq)]
pub struct Instance {
    pub(crate) _inner: BackendInstance,
    pub(crate) module: Module,
    /// The exports for an instance.
    pub exports: Exports,
}
// pub fn hash_cal() {
//
//     let input = "ChainMaker Performance Test";
//     let mut hash_result = [0u8; 32];
//
//     for _ in 0..10000 {
//         let mut hasher = Sha256::new();
//         hasher.update(input.as_bytes());
//         let result = hasher.finalize();
//         hash_result.copy_from_slice(&result);
//     }
// }


/// 从 WASM 内存中读取 UTF-8 字符串
///
/// # Arguments
///
/// * `view` - WASM 内存视图
/// * `start` - 起始偏移地址
/// * `len` - 字符串长度
pub fn read_string(view: &MemoryView, start: i32, len: i32) -> anyhow::Result<String> {
    Ok(WasmPtr::<u8>::new(start as u32).read_utf8_string(view, len as u32)?)
}
// enum MeteringPoints {
//     /// The given number of metering points is left for the execution.
//     /// If the value is 0, all points are consumed but the execution
//     /// was not terminated.
//     Remaining(u64),
//
//     /// The execution was terminated because the metering points were
//     /// exhausted.  You can recover from this state by setting the
//     /// points via [`set_remaining_points`] and restart the execution.
//     Exhausted,
// }
/// ChenHang 进一步地代码下沉
/// Host 环境结构体，用于传递 WASM 内存引用
pub struct ExampleEnv {
    memory: Option<Memory>,
    metering_remaining_points: Option<Global>,
    metering_points_exhausted: Option<Global>,
}

impl ExampleEnv {
    fn set_memory(&mut self, memory: Memory) {
        self.memory = Some(memory);
    }

    fn get_memory(&self) -> &Memory {
        self.memory.as_ref().unwrap()
    }

    fn view<'a>(&'a self, store: &'a impl AsStoreRef) -> MemoryView<'a> {
        self.get_memory().view(store)
    }


    // fn set_metering_globals(&mut self, remaining: Global, exhausted: Global) {
    //     self.metering_remaining_points = Some(remaining);
    //     self.metering_points_exhausted = Some(exhausted);
    // }
    //
    // fn set_remaining_points(&self, ctx: &mut impl AsStoreMut, points: u64) {
    //     self.metering_remaining_points
    //         .as_ref()
    //         .expect("Metering remaining points global not set")
    //         .set(ctx, points.into())
    //         .expect("Failed to set remaining points");
    //
    //     self.metering_points_exhausted
    //         .as_ref()
    //         .expect("Metering points exhausted global not set")
    //         .set(ctx, 0i32.into())
    //         .expect("Failed to reset points exhausted");
    // }
    //
    // fn get_remaining_points(&self, ctx: &mut impl AsStoreMut) -> MeteringPoints {
    //     let exhausted: i32 = self
    //         .metering_points_exhausted
    //         .as_ref()
    //         .expect("Metering points exhausted global not set")
    //         .get(ctx)
    //         .try_into()
    //         .expect("Metering points exhausted global has wrong type");
    //
    //     if exhausted > 0 {
    //         return MeteringPoints::Exhausted;
    //     }
    //
    //     let points: u64 = self
    //         .metering_remaining_points
    //         .as_ref()
    //         .expect("Metering remaining points global not set")
    //         .get(ctx)
    //         .try_into()
    //         .expect("Metering remaining points global has wrong type");
    //
    //     MeteringPoints::Remaining(points)
    // }


}
/// Native SHA256 实现
fn native_sha256(mut ctx: FunctionEnvMut<ExampleEnv>, input_ptr: i32, input_len: i32, result_ptr: i32) -> i32 {
    // 获取 WASM 内存视图
    let view = ctx.data().view(&ctx);
    // 读取字符串
    let input_data = match read_string(&view, input_ptr, input_len) {
        Ok(s) => s,
        Err(_) => return -1,//读取字符串失败
    };
    // 执行 SHA256 哈希计算
    let mut hasher = Sha256::new();
    hasher.update(input_data.as_bytes());
    let result = hasher.finalize();

    // 将哈希结果写回内存
    let result_bytes = result.to_vec();
    if view.write(result_ptr as u64, &result_bytes).is_err() {
        return -5;
    }

    // 作用域 2：可以安全地 mut ctx
    // let data = ctx.data_mut();
    // data.set_remaining_points(&mut ctx, 1000);
    // 返回 0 表示成功,-1 表示失败
    0
}
/// Native parse_int 实现, 等价于go的strconv.ParesInt，支持进制转换
/// 将字符串转换成int64
fn native_parse_int64(
    mut ctx: FunctionEnvMut<ExampleEnv>,
    input_ptr: i32,
    input_len: i32,
    base: i32,
    bit_size: i32,
    result_ptr: i32,
) -> i32 {
    let view = ctx.data().view(&ctx);

    // 读取字符串
    let input = match read_string(&view, input_ptr, input_len) {
        Ok(s) => s,
        Err(_) => return -1,
    };

    let parse_result = if bit_size <= 32 {
        i32::from_str_radix(&input, base as u32).map(|v| v as i64)
    } else {
        i64::from_str_radix(&input, base as u32)
    };

    let value = match parse_result {
        Ok(val) => val,
        Err(_) => return -2,
    };

    // 写入结果：小端字节序写入 8 字节
    let bytes = value.to_le_bytes();
    if view.write(result_ptr as u64, &bytes).is_err() {
        return -5;
    }
    // 返回 0 表示成功
    0
}


/// native_big_exp 实现, 等价于go的new(big.Int).Exp
fn native_big_exp(
    mut ctx: FunctionEnvMut<ExampleEnv>,
    num: i64,
    exp: i64,
    modu: i64,
    result_ptr: i32,
) -> i32 {
    let view = ctx.data().view(&ctx);

    // 构造大整数
    let base = BigInt::from(num);
    let exponent = BigInt::from(exp);
    // 结果字节
    let result_bytes: Vec<u8>;
    // 判断 modulus
    if modu == 0 {

        if exponent < BigInt::from(0) {
            // 负指数且无模，参考Go 会返回 1
            result_bytes = b"1".to_vec();
        } else {
            // 无膜，且指数为正，正常求幂不模
            let Some(exp_u32) = exponent.to_u32() else {
                return -1; // exponent 太大，转换失败
            };
            let result = base.pow(exp_u32);
            result_bytes = result.to_signed_bytes_be();
        }
    } else {
        let modulus = BigInt::from(modu);

        // exponent 负数在 Rust 会 panic，Go 的 Exp 是能处理的（会尝试求模逆）
        if exponent < BigInt::from(0) {
            return -2;//exponent为负数
        }

        let result = base.modpow(&exponent, &modulus);
        result_bytes = result.to_signed_bytes_be();
    }

    if result_bytes.len() > 256 {
        return -5; // 太大写入内存失败
    }
    // 写入到 WASM 内存
    if view.write(result_ptr as u64, &result_bytes).is_ok() {
        result_bytes.len() as i32 // 成功
    } else {
        -5 // 写入内存失败
    }
}


// /// native_format_int 实现, 等价于go的strconv.FormatInt,整数转字符串，支持进制转换
// /// // FormatInt returns the string representation of i in the given base,
// /// // for 2 <= base <= 36. The result uses the lower-case letters 'a' to 'z'
// /// // for digit values >= 10.
// fn native_format_int64(
//     mut ctx: FunctionEnvMut<ExampleEnv>,
//     value: i64,
//     base: i32,
//     output_ptr: i32,
//     max_len: i32,
// ) -> i32 {
//     let view = ctx.data().view(&ctx);
//
//     let val = i64::from_le_bytes(value.to_le_bytes());
//
//     // 转换为字符串
//     let s = match format_radix(val, base) {
//         Ok(s) => s,
//         Err(_) => return -1,
//     };
//
//     let bytes = s.as_bytes();
//     if bytes.len() > max_len as usize {
//         return -1;
//     }
//
//     if view.write(output_ptr as u64, bytes).is_err() {
//         return -1;
//     }
//
//     let ret=bytes.len().to_i32();
//     ret.unwrap()
// }
//
// // 用于处理非法 base 情况
// fn format_radix(val: i64, base: i32) -> Result<String, ()> {
//     match base {
//         2..=36 => Ok(format!("{:x}", val).to_uppercase()),
//         _ => Err(()),
//     }
// }



impl Instance {
    /// Creates a new `Instance` from a WebAssembly [`Module`] and a
    /// set of imports using [`Imports`] or the [`imports!`] macro helper.
    ///
    /// [`imports!`]: crate::imports!
    /// [`Imports!`]: crate::Imports!
    ///
    /// ```
    /// # use wasmer::{imports, Store, Module, Global, Value, Instance};
    /// # use wasmer::FunctionEnv;
    /// # fn main() -> anyhow::Result<()> {
    /// let mut store = Store::default();
    /// let env = FunctionEnv::new(&mut store, ());
    /// let module = Module::new(&store, "(module)")?;
    /// let imports = imports!{
    ///   "host" => {
    ///     "var" => Global::new(&mut store, Value::I32(2))
    ///   }
    /// };
    /// let instance = Instance::new(&mut store, &module, &imports)?;
    /// # Ok(())
    /// # }
    /// ```
    ///
    /// ## Errors
    ///
    /// The function can return [`InstantiationError`]s.
    ///
    /// Those are, as defined by the spec:
    ///  * Link errors that happen when plugging the imports into the instance
    ///  * Runtime errors that happen when running the module `start` function.
    #[allow(clippy::result_large_err)]
    pub fn new(
        store: &mut impl AsStoreMut,
        module: &Module,
        imports:&Imports,
    ) -> Result<Self, InstantiationError> {
        let mut import_object=imports.clone();;
        //在实例化前注入这里
        // let function_env = FunctionEnv::new(store, ExampleEnv { memory: None });
        // import_object.define("env","native_sha", Function::new_typed_with_env(store, &function_env, native_sha256));
        let (_inner, exports) = match &store.as_store_mut().inner.store {

            #[cfg(feature = "sys")]
            crate::BackendStore::Sys(_) => {
                let (i, e) = crate::backend::sys::instance::Instance::new(store, module, &import_object)?;
                (crate::BackendInstance::Sys(i), e)
            }
            #[cfg(feature = "wamr")]
            crate::BackendStore::Wamr(_) => {
                let (i, e) = crate::backend::wamr::instance::Instance::new(store, module, &import_object)?;

                (crate::BackendInstance::Wamr(i), e)
            }
            #[cfg(feature = "wasmi")]
            crate::BackendStore::Wasmi(_) => {
                let (i, e) =
                    crate::backend::wasmi::instance::Instance::new(store, module, &import_object)?;

                (crate::BackendInstance::Wasmi(i), e)
            }
            #[cfg(feature = "v8")]
            crate::BackendStore::V8(_) => {
                let (i, e) = crate::backend::v8::instance::Instance::new(store, module, &import_object)?;
                (crate::BackendInstance::V8(i), e)
            }
            #[cfg(feature = "js")]
            crate::BackendStore::Js(_) => {
                let (i, e) = crate::backend::js::instance::Instance::new(store, module, &import_object)?;
                (crate::BackendInstance::Js(i), e)
            }
            #[cfg(feature = "jsc")]
            crate::BackendStore::Jsc(_) => {
                let (i, e) = crate::backend::jsc::instance::Instance::new(store, module, &import_object)?;
                (crate::BackendInstance::Jsc(i), e)
            }
        };
        // let memory = exports
        //     .get_memory("memory")
        //     .map_err(|e| InstantiationError::Start(RuntimeError::new(e.to_string())))?;
        // // Give reference to memory
        // function_env.as_mut(store).set_memory(memory.clone());
        Ok(Self {
            _inner,
            module: module.clone(),
            exports,
        })
    }

    /// Creates a new `Instance` from a WebAssembly [`Module`] and a
    /// vector of imports.
    ///
    /// ## Errors
    ///
    /// The function can return [`InstantiationError`]s.
    ///
    /// Those are, as defined by the spec:
    ///  * Link errors that happen when plugging the imports into the instance
    ///  * Runtime errors that happen when running the module `start` function.
    /// chenhang 修改，添加进一步代码下沉的注入操作
    #[allow(clippy::result_large_err)]
    pub fn new_by_index(
        store: &mut impl AsStoreMut,
        module: &Module,
        externs: &[Extern],
    ) -> Result<Self, InstantiationError> {
        let function_env = FunctionEnv::new(store, ExampleEnv { memory: None,metering_points_exhausted:None,metering_remaining_points:None });

        let native_sha = Function::new_typed_with_env(store, &function_env, native_sha256);
        let native_sha_extern = Extern::Function(native_sha);
        let native_parse_int64 = Function::new_typed_with_env(store, &function_env, crate::entities::instance::native_parse_int64);
        let native_parse_int64_extern = Extern::Function(native_parse_int64);
        let native_big_exp = Function::new_typed_with_env(store, &function_env, crate::entities::instance::native_big_exp);
        let native_big_exp_extern = Extern::Function(native_big_exp);

        let mut final_externs = Vec::new();
        let mut extern_iter = externs.iter();
        // 定义你要注入的函数映射（可以扩展多个）
        let mut injected_funcs = std::collections::HashMap::new();
        injected_funcs.insert(
            ("env".to_string(), "native_sha".to_string()),
            native_sha_extern,
        );
        injected_funcs.insert(
            ("env".to_string(), "native_parse_int".to_string()),
            native_parse_int64_extern,
        );
        injected_funcs.insert(
            ("env".to_string(), "native_big_exp".to_string()),
            native_big_exp_extern,
        );
        let mut flag=false;
        // 遍历 module 的导入项，逐个构造对应的 Extern
        for import in module.imports() {
            let key = (import.module().to_string(), import.name().to_string());
            //如果module.imports里要求注入则注入
            if let Some(custom_extern) = injected_funcs.get(&key) {
                final_externs.push(custom_extern.clone());
                flag=true;
            } else {
                // 不是我们要注入的函数，就使用原始 externs 的下一个
                if let Some(ext) = extern_iter.next() {
                    final_externs.push(ext.clone());
                }
            }
        }


        let (_inner, exports) = match &store.as_store_mut().inner.store {
            #[cfg(feature = "sys")]
            crate::BackendStore::Sys(_) => {
                let (i, e) =
                    crate::backend::sys::instance::Instance::new_by_index(store, module, &final_externs)?;
                (crate::BackendInstance::Sys(i), e)
            }
            #[cfg(feature = "wamr")]
            crate::BackendStore::Wamr(_) => {
                let (i, e) =
                    crate::backend::wamr::instance::Instance::new_by_index(store, module, &final_externs)?;

                (crate::BackendInstance::Wamr(i), e)
            }
            #[cfg(feature = "wasmi")]
            crate::BackendStore::Wasmi(_) => {
                let (i, e) = crate::backend::wasmi::instance::Instance::new_by_index(
                    store, module, &final_externs,
                )?;

                (crate::BackendInstance::Wasmi(i), e)
            }
            #[cfg(feature = "v8")]
            crate::BackendStore::V8(_) => {
                let (i, e) =
                    crate::backend::v8::instance::Instance::new_by_index(store, module, &final_externs)?;
                (crate::BackendInstance::V8(i), e)
            }
            #[cfg(feature = "js")]
            crate::BackendStore::Js(_) => {
                let (i, e) =
                    crate::backend::js::instance::Instance::new_by_index(store, module, &final_externs)?;
                (crate::BackendInstance::Js(i), e)
            }
            #[cfg(feature = "jsc")]
            crate::BackendStore::Jsc(_) => {
                let (i, e) =
                    crate::backend::jsc::instance::Instance::new_by_index(store, module, &final_externs)?;
                (crate::BackendInstance::Jsc(i), e)
            }
        };
        if flag {
            let memory = exports
                .get_memory("memory")
                .map_err(|e| InstantiationError::Start(RuntimeError::new(e.to_string())))?;
            // Give reference to memory
            function_env.as_mut(store).set_memory(memory.clone());
            // // 取两个 global
            // let remaining_points = exports
            //     .get_global("wasmer_metering_remaining_points")
            //     .map_err(|e| InstantiationError::Start(RuntimeError::new(e.to_string())))?;
            //
            // let points_exhausted = exports
            //     .get_global("wasmer_metering_points_exhausted")
            //     .map_err(|e| InstantiationError::Start(RuntimeError::new(e.to_string())))?;
            //
            // function_env.as_mut(store).set_metering_globals(remaining_points.clone(), points_exhausted.clone());
        }

        Ok(Self {
            _inner,
            module: module.clone(),
            exports,
        })
    }



    /// Gets the [`Module`] associated with this instance.
    pub fn module(&self) -> &Module {
        &self.module
    }
}

impl std::fmt::Debug for Instance {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        f.debug_struct("Instance")
            .field("exports", &self.exports)
            .finish()
    }
}

/// An enumeration of all the possible instances kind supported by the runtimes.
gen_rt_ty!(Instance @derives Clone, PartialEq, Eq);
