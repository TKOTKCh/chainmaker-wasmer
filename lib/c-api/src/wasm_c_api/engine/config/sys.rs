// Necessary when a single backend is enabled.
#![allow(irrefutable_let_patterns)]

use std::ptr::NonNull;
use crate::{
    error::update_last_error,
    wasm_c_api::engine::{
        wasm_config_t, wasm_engine_t, wasmer_backend_config_kind_t, wasmer_backend_t,
    },
};


#[cfg(feature = "middlewares")]
pub use crate::wasm_c_api::unstable::middlewares::wasmer_middleware_t;

use cfg_if::cfg_if;
#[cfg(any(feature = "compiler", feature = "compiler-headless"))]
use wasmer_api::Engine;
#[cfg(any(feature = "compiler", feature = "compiler-headless"))]
use wasmer_compiler::EngineBuilder;

#[cfg(feature = "compiler")]
use wasmer_api::sys::CompilerConfig;
use wasmer_api::sys::NativeEngineExt;
use wasmer_api::sys::vm::{VMMemory, VMMemoryDefinition, VMTable, VMTableDefinition};
use wasmer_compiler::{BaseTunables, Tunables};
use wasmer_types::{MemoryError, MemoryStyle, MemoryType, Pages, TableStyle, TableType};
use wasmer_types::target::Target;

/// Configuration specific for `sys` (Cranelift, LLVM, Singlepass) engines.
///
/// This is a Wasmer-specific type with Wasmer-specific functions for manipulating it.
///
/// cbindgen:ignore
#[repr(C)]
#[derive(Debug, Default)]
pub(crate) struct wasmer_sys_engine_config_t {
    pub nan_canonicalization: bool,
}

/// Updates the configuration to enable NaN canonicalization.
///
/// This is a Wasmer-specific function.
///
/// # Example
///
/// ```rust
/// # use wasmer_inline_c::assert_c;
/// # fn main() {
/// #    (assert_c! {
/// # #include "tests/wasmer.h"
/// #
/// int main() {
///     // Create the configuration.
///     wasm_config_t* config = wasm_config_new();
///
///     // Enable NaN canonicalization.
///     wasm_config_sys_canonicalize_nans(config, true);
///
///     // Create the engine.
///     wasm_engine_t* engine = wasm_engine_new_with_config(config);
///
///     // Check we have an engine!
///     assert(engine);
///
///     // Free everything.
///     wasm_engine_delete(engine);
///
///     return 0;
/// }
/// #    })
/// #    .success();
/// # }
/// ```
#[no_mangle]
pub extern "C" fn wasm_config_sys_canonicalize_nans(config: &mut wasm_config_t, enable: bool) {
    if let wasmer_backend_config_kind_t::Sys(ref mut c) = config.backend_config.inner {
        c.nan_canonicalization = enable;
    } else {
        let sys_config = wasmer_sys_engine_config_t {
            nan_canonicalization: enable,
        };
        config.backend_config.inner = wasmer_backend_config_kind_t::Sys(sys_config);
    }
}

pub struct LimitingTunables<T: Tunables> {
    /// The maximum a linear memory is allowed to be (in Wasm pages, 64 KiB each).
    /// Since Wasmer ensures there is only none or one memory, this is practically
    /// an upper limit for the guest memory.
    limit: Pages,
    /// The base implementation we delegate all the logic to
    base: T,
}

impl<T: Tunables> LimitingTunables<T> {
    pub fn new(base: T, limit: Pages) -> Self {
        Self { limit, base }
    }

    /// Takes an input memory type as requested by the guest and sets
    /// a maximum if missing. The resulting memory type is final if
    /// valid. However, this can produce invalid types, such that
    /// validate_memory must be called before creating the memory.
    fn adjust_memory(&self, requested: &MemoryType) -> MemoryType {
        let mut adjusted = requested.clone();
        //如果wasm指令没有要求内存上限，则用注入的内存上限
        if requested.maximum.is_none() {
            adjusted.maximum = Some(self.limit);
        }else{
            // chenhang新增，如果wasm指令要求的内存上限比注入的内存上限大，则用注入的内存上限
            if requested.maximum.unwrap() > self.limit {
                adjusted.maximum = Some(self.limit);
            }
        }
        adjusted
    }

    /// Ensures the a given memory type does not exceed the memory limit.
    /// Call this after adjusting the memory.
    fn validate_memory(&self, ty: &MemoryType) -> Result<(), MemoryError> {
        if ty.minimum > self.limit {
            return Err(MemoryError::Generic(
                "Minimum exceeds the allowed memory limit".to_string(),
            ));
        }

        if let Some(max) = ty.maximum {
            if max > self.limit {
                return Err(MemoryError::Generic(
                    "Maximum exceeds the allowed memory limit".to_string(),
                ));
            }
        } else {
            return Err(MemoryError::Generic("Maximum unset".to_string()));
        }

        Ok(())
    }
}

impl<T: Tunables> Tunables for LimitingTunables<T> {
    /// Construct a `MemoryStyle` for the provided `MemoryType`
    ///
    /// Delegated to base.
    fn memory_style(&self, memory: &MemoryType) -> MemoryStyle {
        let adjusted = self.adjust_memory(memory);
        self.base.memory_style(&adjusted)
    }

    /// Construct a `TableStyle` for the provided `TableType`
    ///
    /// Delegated to base.
    fn table_style(&self, table: &TableType) -> TableStyle {
        self.base.table_style(table)
    }

    /// Create a memory owned by the host given a [`MemoryType`] and a [`MemoryStyle`].
    ///
    /// The requested memory type is validated, adjusted to the limited and then passed to base.
    fn create_host_memory(
        &self,
        ty: &MemoryType,
        style: &MemoryStyle,
    ) -> Result<VMMemory, MemoryError> {
        let adjusted = self.adjust_memory(ty);
        self.validate_memory(&adjusted)?;
        self.base.create_host_memory(&adjusted, style)
    }

    /// Create a memory owned by the VM given a [`MemoryType`] and a [`MemoryStyle`].
    ///
    /// Delegated to base.
    unsafe fn create_vm_memory(
        &self,
        ty: &MemoryType,
        style: &MemoryStyle,
        vm_definition_location: NonNull<VMMemoryDefinition>,
    ) -> Result<VMMemory, MemoryError> {
        let adjusted = self.adjust_memory(ty);
        self.validate_memory(&adjusted)?;
        self.base
            .create_vm_memory(&adjusted, style, vm_definition_location)
    }

    /// Create a table owned by the host given a [`TableType`] and a [`TableStyle`].
    ///
    /// Delegated to base.
    fn create_host_table(&self, ty: &TableType, style: &TableStyle) -> Result<VMTable, String> {
        self.base.create_host_table(ty, style)
    }

    /// Create a table owned by the VM given a [`TableType`] and a [`TableStyle`].
    ///
    /// Delegated to base.
    unsafe fn create_vm_table(
        &self,
        ty: &TableType,
        style: &TableStyle,
        vm_definition_location: NonNull<VMTableDefinition>,
    ) -> Result<VMTable, String> {
        self.base.create_vm_table(ty, style, vm_definition_location)
    }
}

/// Create a new  [`wasm_engine_t`] backed by a `sys` engine.
pub fn wasm_sys_engine_new_with_config(config: wasm_config_t) -> Option<Box<wasm_engine_t>> {
    if !matches!(config.backend, wasmer_backend_t::LLVM)
        && !matches!(config.backend, wasmer_backend_t::SINGLEPASS)
        && !matches!(config.backend, wasmer_backend_t::CRANELIFT)
        && !matches!(config.backend, wasmer_backend_t::HEADLESS)
        && !config.backend_config.inner.is_sys()
    {
        update_last_error(format!(
            "Cannot create a new `sys` engine with a non-sys-specific config! {config:?}"
        ));
        return None;
    }

    let backend = config.backend;
    #[allow(unused)]
    let sys_config = match config.backend_config.inner.try_into_sys() {
        Err(_) => {
            update_last_error(format!(
                "Could not create new `sys` engine with the selected {backend:?} backend."
            ));
            return None;
        }
        Ok(s) => s,
    };

    cfg_if! {
    if #[cfg(feature = "compiler")] {
                #[allow(unused_mut)]
                let mut compiler_config: Box<dyn CompilerConfig> = match &backend {
                    wasmer_backend_t::CRANELIFT => {
                        cfg_if! {
                            if #[cfg(feature = "cranelift")] {
                                Box::<wasmer_compiler_cranelift::Cranelift>::default()
                            } else {
                                update_last_error("Wasmer has not been compiled with the `cranelift` feature.");
                                return None;
                            }
                        }
                    },
                    wasmer_backend_t::LLVM => {
                        cfg_if! {
                            if #[cfg(feature = "llvm")] {
                                Box::<wasmer_compiler_llvm::LLVM>::default()
                            } else {
                                update_last_error("Wasmer has not been compiled with the `llvm` feature.");
                                return None;
                            }
                        }
                    },
                    wasmer_backend_t::SINGLEPASS => {
                        cfg_if! {
                            if #[cfg(feature = "singlepass")] {
                                Box::<wasmer_compiler_singlepass::Singlepass>::default()
                            } else {
                                update_last_error("Wasmer has not been compiled with the `singlepass` feature.");
                                return None;
                            }
                        }
                    },
                    _ => panic!("not a `sys` backend!")
                };

                #[cfg(feature = "middlewares")]
                for middleware in config.backend_config.middlewares {
                    compiler_config.push_middleware(middleware.inner.clone());
                }

                if sys_config.nan_canonicalization {
                    compiler_config.canonicalize_nans(true);
                }

                let mut inner: Engine =
                             {
                                let mut builder = EngineBuilder::new(compiler_config);

                                if let Some(target) = config.backend_config.target {
                                    builder = builder.set_target(Some(target.inner));
                                }

                                if let Some(features) = config.features {
                                    builder = builder.set_features(Some(features.inner));
                                }

                                builder.engine().into()
                            };
                let base = BaseTunables::for_target(&Target::default());
                let limit_pages = if config.max_memory_pages != 0 {
                    config.max_memory_pages
                } else {
                    256 // 默认值：256 页 = 16 MiB
                };

                let tunables = LimitingTunables::new(base, Pages(limit_pages));
                inner.set_tunables(tunables);
                Some(Box::new(wasm_engine_t { inner }))
            } else if #[cfg(feature = "compiler-headless")] {
                let inner: Engine =
                         {
                                let mut builder = EngineBuilder::headless();

                                if let Some(target) = config.backend_config.target {
                                    builder = builder.set_target(Some(target.inner));
                                }

                                if let Some(features) = config.features {
                                    builder = builder.set_features(Some(features.inner));
                                }

                                builder.engine().into()
                        };

                Some(Box::new(wasm_engine_t { inner }))
            } else {
                update_last_error("No backend enabled for the `sys` engine: enable one of `compiler` or `compiler-headless`!");
                return None;
            }
        }
}

impl wasmer_backend_config_kind_t {
    /// Returns `true` if the wasmer_engine_config_t is [`Sys`].
    ///
    /// [`Sys`]: wasmer_engine_config_t::Sys
    #[must_use]
    pub(super) fn is_sys(&self) -> bool {
        matches!(self, Self::Sys(..))
    }

    pub(super) fn try_into_sys(self) -> Result<wasmer_sys_engine_config_t, Self> {
        if let Self::Sys(v) = self {
            Ok(v)
        } else {
            Err(self)
        }
    }
}
