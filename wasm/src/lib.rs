// TODO(evaluator-removal): this crate's `run_file`/`WasmRepl::eval` used
// to evaluate via the legacy tree-walking evaluator (`monad_core::eval::
// eval`/`monad_core::eval::r#type::type_check`), which has been removed
// now that `core_eval`/`core_native` (the CoreTerm evaluator) is the
// sole production evaluator. This crate was never ported to that
// pipeline (it's the one real, independent consumer that still needed
// it) — both functions below currently return a clear "not supported"
// `WasmResult` instead of evaluating anything. Porting them means
// following the same `build_core_program` -> `lower_core_ir::
// lower_program` -> `core_value::{NativeTable,GlobalTable,GlobalCache}`
// -> `core_eval::force_global` pipeline `core/src/lib.rs`'s `run()`/
// `eval_repl_term()` already use — see those for the reference shape.
// Module/decl loading (`use`, adding a def to the REPL's scratch
// module) is untouched below and still works; only the "evaluate a
// term" path is stubbed.

use monad_core::parser::{ReplInput, repl_parser};
use monad_core::term::Decl;
use monad_core::term::module::{ParsedModule, default_modules, load_module_files, module};
use monad_core::term::ModulePath;
use wasm_bindgen::prelude::*;

#[cfg(feature = "console_error_panic_hook")]
pub fn set_panic_hook() {
  console_error_panic_hook::set_once();
}

#[wasm_bindgen(start)]
pub fn start() {
  #[cfg(feature = "console_error_panic_hook")]
  set_panic_hook();
}

#[wasm_bindgen]
pub struct WasmResult {
  value: String,
  error: Option<String>,
}

#[wasm_bindgen]
impl WasmResult {
  #[wasm_bindgen(getter)]
  pub fn value(&self) -> String {
    self.value.clone()
  }

  #[wasm_bindgen(getter)]
  pub fn error(&self) -> Option<String> {
    self.error.clone()
  }

  #[wasm_bindgen(getter)]
  pub fn is_ok(&self) -> bool {
    self.error.is_none()
  }
}

fn not_yet_supported() -> WasmResult {
  WasmResult {
    value: String::new(),
    error: Some(
      "the wasm playground's evaluator hasn't been ported to the CoreTerm evaluator yet \
       (see the TODO at the top of wasm/src/lib.rs)"
        .to_string(),
    ),
  }
}

#[wasm_bindgen]
pub fn run_file(_path: String, _args: JsValue) -> WasmResult {
  not_yet_supported()
}

#[wasm_bindgen]
pub struct WasmRepl {
  loaded: monad_core::term::module::LoadedModules,
  module_path: ModulePath,
}

#[wasm_bindgen]
impl WasmRepl {
  #[wasm_bindgen(constructor)]
  pub fn new() -> WasmRepl {
    let mut loaded = default_modules().unwrap();
    let module_path = ModulePath::top("'wasm");
    let module = module(
      module_path.clone(),
      ParsedModule {
        decls: vec![],
        module_doc: None,
      },
    );
    loaded.add_module(module);
    WasmRepl {
      loaded,
      module_path,
    }
  }

  pub fn eval(&mut self, source: String) -> WasmResult {
    let parsed = match repl_parser(&source) {
      Ok(r) => r,
      Err(e) => {
        return WasmResult {
          value: String::new(),
          error: Some(format!("Parse error: {}", e)),
        };
      }
    };

    match parsed {
      ReplInput::Term(_term) => not_yet_supported(),
      ReplInput::Decls(Decl::Use(u)) => {
        if self.loaded.get_module(u.module_path()).is_some() {
          WasmResult {
            value: format!("Module '{}' already loaded", u.module_path()),
            error: None,
          }
        } else {
          let loaded = self.loaded.clone();
          match load_module_files(u.module_path(), loaded) {
            Ok(new_loaded) => {
              self.loaded = new_loaded;
              WasmResult {
                value: format!("Loaded module '{}'", u.module_path()),
                error: None,
              }
            }
            Err(e) => WasmResult {
              value: String::new(),
              error: Some(format!("Loading error: {}", e)),
            },
          }
        }
      }
      ReplInput::Decls(decl) => {
        self
          .loaded
          .get_module_mut(&self.module_path)
          .unwrap()
          .add_decl(decl);
        WasmResult {
          value: "Definition added".to_string(),
          error: None,
        }
      }
    }
  }
}
