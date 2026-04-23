use monad_core::eval::r#type::type_check;
use monad_core::eval::{EvalOptions, eval};
use monad_core::parser::parse_term;
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
pub fn eval_term(source: String) -> WasmResult {
  let options = EvalOptions { debug: false };

  let mut loaded = match default_modules() {
    Ok(m) => m,
    Err(e) => {
      return WasmResult {
        value: String::new(),
        error: Some(e.to_string()),
      };
    }
  };

  let module_path = ModulePath::top("'wasm");
  let module = module(module_path.clone(), vec![]);
  loaded.add_module(module);
  let global = match loaded.global(&module_path) {
    Some(g) => g,
    None => {
      return WasmResult {
        value: String::new(),
        error: Some("Failed to create global scope".into()),
      };
    }
  };

  let parsed = match parse_term(&source) {
    Ok(t) => t,
    Err(e) => {
      return WasmResult {
        value: String::new(),
        error: Some(format!("Parse error: {}", e)),
      };
    }
  };

  let result = match type_check(parsed, Hole, &global.scope()) {
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
