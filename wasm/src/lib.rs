use monad_core::eval::r#type::type_check;
use monad_core::eval::{EvalOptions, eval};
use monad_core::parser::{ReplInput, repl_parser};
use monad_core::term::Decl;
use monad_core::term::Term::Hole;
use monad_core::term::module::{default_modules, load_module_files, module};
use monad_core::term::{ModulePath, Term, mpt, strings_to_list_term};
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

#[wasm_bindgen]
pub fn run_file(path: String, args: JsValue) -> WasmResult {
  let args: Vec<String> = serde_wasm_bindgen::from_value(args).unwrap_or_default();
  let options = EvalOptions { debug: false };

  let path: ModulePath = ModulePath::top(&path);
  let mut loaded = match default_modules() {
    Ok(m) => m,
    Err(e) => {
      return WasmResult {
        value: String::new(),
        error: Some(e.to_string()),
      };
    }
  };

  loaded = match load_module_files(&path, loaded) {
    Ok(m) => m,
    Err(e) => {
      return WasmResult {
        value: String::new(),
        error: Some(e.to_string()),
      };
    }
  };

  let module = match loaded.get_module(&path) {
    Some(m) => m,
    None => {
      return WasmResult {
        value: String::new(),
        error: Some("Module not found".into()),
      };
    }
  };

  let global = match loaded.global(&path) {
    Some(g) => g,
    None => {
      return WasmResult {
        value: String::new(),
        error: Some("Module not loaded".into()),
      };
    }
  };

  let def = match module.get_def(&mpt("main")) {
    Some(d) => d,
    None => {
      return WasmResult {
        value: String::new(),
        error: Some("main not found".into()),
      };
    }
  };

  let arg: Term = strings_to_list_term(args);
  let input_term = if def.value().term.is_lam() {
    monad_core::term::app(def.value().term.clone(), arg)
  } else {
    def.value().term.clone()
  };

  let result = match type_check(input_term, Hole, &global.scope()) {
    Ok(tt) => {
      let (term, typ) = tt.to_tuple();
      match eval(term, &global.scope(), &options) {
        Ok(t) => Ok(format!("{}\n: {}", t, typ)),
        Err(e) => Err(e.to_string()),
      }
    }
    Err(e) => Err(e.to_string()),
  };

  match result {
    Ok(v) => WasmResult {
      value: v,
      error: None,
    },
    Err(e) => WasmResult {
      value: String::new(),
      error: Some(e),
    },
  }
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
    let module = module(module_path.clone(), vec![]);
    loaded.add_module(module);
    WasmRepl {
      loaded,
      module_path,
    }
  }

  pub fn eval(&mut self, source: String) -> WasmResult {
    let options = EvalOptions { debug: false };

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
      ReplInput::Term(term) => {
        let global = match self.loaded.global(&self.module_path) {
          Some(g) => g,
          None => {
            return WasmResult {
              value: String::new(),
              error: Some("Failed to create global scope".into()),
            };
          }
        };

        let result = match type_check(term, Hole, &global.scope()) {
          Ok(tt) => {
            let (term, typ) = tt.to_tuple();
            match eval(term, &global.scope(), &options) {
              Ok(t) => Ok(format!("{}\n: {}", t, typ)),
              Err(e) => Err(e.to_string()),
            }
          }
          Err(e) => Err(e.to_string()),
        };

        match result {
          Ok(v) => WasmResult {
            value: v,
            error: None,
          },
          Err(e) => WasmResult {
            value: String::new(),
            error: Some(e),
          },
        }
      }
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

#[cfg(test)]
mod test {
  use monad_core::eval::r#type::{type_check, type_check_module_decls};
  use monad_core::eval::{EvalOptions, eval};
  use monad_core::parser::{ReplInput, repl_parser};
  use monad_core::term::Decl;
  use monad_core::term::Term::Hole;
  use monad_core::term::module::{default_modules, load_module_files, module};
  use monad_core::term::{ModulePath, SourceContext, Term, app, mpt, strings_to_list_term};

  #[derive(serde::Deserialize)]
  struct WebExample {
    name: String,
    code: String,
  }

  fn run_example_repl(code: &str) -> Result<Term, String> {
    let mut loaded = default_modules().unwrap();
    let module_path = ModulePath::top("'test");
    let modl = module(module_path.clone(), vec![]);
    loaded.add_module(modl);

    let mut decls: Vec<SourceContext<Decl>> = vec![];
    let chunks: Vec<&str> = code
      .split("\n\n")
      .map(|s| s.trim())
      .filter(|s| !s.is_empty())
      .collect();
    for chunk in chunks {
      let parsed = repl_parser(chunk).map_err(|e| format!("parse error: {e}"))?;
      match parsed {
        ReplInput::Term(_) => {}
        ReplInput::Decls(Decl::Use(u)) => {
          decls.push(SourceContext::no_ctx(Decl::Use(u.clone())));
          if loaded.get_module(u.module_path()).is_none() {
            let new_loaded = load_module_files(u.module_path(), loaded.clone())
              .map_err(|e| format!("load error: {e}"))?;
            loaded = new_loaded;
          }
        }
        ReplInput::Decls(decl) => {
          decls.push(SourceContext::no_ctx(decl));
        }
      }
    }

    let decls = type_check_module_decls(&module_path, decls, &mut loaded)
      .map_err(|e| format!("type error: {e}"))?;
    let modl = module(module_path.clone(), decls);
    loaded.add_module(modl);

    let global = loaded.global(&module_path).ok_or("global scope failed")?;
    let module = loaded.get_module(&module_path).ok_or("module not found")?;
    let def = module
      .get_def(&mpt("main"))
      .ok_or("main not found")?
      .value();
    let input_term = if def.term.is_lam() {
      app(def.term.clone(), strings_to_list_term(vec![]))
    } else {
      def.term.clone()
    };

    let (term, _typ) = type_check(input_term, Hole, &global.scope())
      .map_err(|e| format!("type check error: {e}"))?
      .to_tuple();

    eval(term, &global.scope(), &EvalOptions { debug: false })
      .map_err(|e| format!("eval error: {e}"))
  }

  #[test]
  fn test_web_repl_examples() {
    let examples_json =
      std::fs::read_to_string("web/examples.json").expect("web/examples.json not found");
    let examples: Vec<WebExample> =
      serde_json::from_str(&examples_json).expect("failed to parse examples.json");

    for example in &examples {
      let result = run_example_repl(&example.code);
      assert!(
        result.is_ok(),
        "Example '{}' failed: {:?}",
        example.name,
        result.err()
      );
    }
  }
}
