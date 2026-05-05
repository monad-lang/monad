use std::collections::{BTreeMap, HashSet};
use std::fmt::Display;
use std::hash::{BuildHasherDefault, DefaultHasher, Hash};
use std::path::PathBuf;

use crate::eval::r#type::type_check;
use crate::eval::{EvalOptions, eval};
#[cfg(feature = "repl")]
use crate::parser::{ReplInput, repl_parser};
#[cfg(feature = "repl")]
use crate::term::Decl;
use crate::term::Term::{self, Con, Hole};
#[cfg(feature = "repl")]
use crate::term::module::ParsedModule;
#[cfg(feature = "repl")]
use crate::term::module::module;
use crate::term::module::{default_modules, load_module_files};
use crate::term::{Constructor, ModulePath, mpt, strings_to_list_term};
use crate::term::{app, id};

pub mod eval;
pub mod parser;
pub mod term;

#[cfg(all(not(target_arch = "wasm32"), feature = "repl"))]
use rustyline::{DefaultEditor, error::ReadlineError};

pub type Set<T> = HashSet<T, BuildHasherDefault<DefaultHasher>>;
pub fn empty_set<T: Eq + Hash>() -> Set<T> {
  HashSet::with_hasher(BuildHasherDefault::new())
}

pub fn set_of<T: Eq + Hash>(vals: impl Iterator<Item = T>) -> Set<T> {
  let mut set = empty_set();
  for value in vals {
    set.insert(value);
  }
  set
}

pub type Map<K, V> = BTreeMap<K, V>;

#[cfg(all(not(target_arch = "wasm32"), feature = "repl"))]
pub fn repl(options: EvalOptions) -> Result<(), String> {
  let mut rl = DefaultEditor::new().map_err(|e| format!("{e}"))?;

  if rl.load_history("history.txt").is_err() {
    println!("No previous history.");
  }
  let mut loaded_modules = default_modules().map_err(|e| format!("{e}"))?;
  let module_path = ModulePath::top("'repl");
  let module = module(
    module_path.clone(),
    ParsedModule {
      decls: vec![],
      module_doc: None,
    },
  );
  loaded_modules.add_module(module);
  let mut loaded_scopes = loaded_modules.scopes();
  let mut global = loaded_scopes.global(&module_path).unwrap();
  loop {
    let readline = rl.readline(">> ");
    match readline {
      Ok(line) => {
        let repl_res = repl_parser(&line).map_err(|e| format!("{e}"));
        match repl_res {
          Err(e) => eprintln!("error: {e}"),
          Ok(repl_input) => {
            if options.debug {
              println!("Parsed: {repl_input}");
            }
            rl.add_history_entry(line.as_str())
              .map_err(|e| format!("{e}"))?;

            match repl_input {
              ReplInput::Term(term) => {
                let scope = global.scope();
                let t = type_check(term, Hole, &scope);
                match t {
                  Ok(tt) => {
                    let (term, typ) = tt.to_tuple();
                    println!("Eval type {typ}");

                    let term = eval(term, &scope, &options);
                    match term {
                      Ok(t) => println!("{t}"),
                      Err(e) => eprintln!("error: {e}"),
                    }
                  }
                  Err(e) => eprintln!("Type error: {e}"),
                }
              }
              ReplInput::Decls(Decl::Use(u)) => {
                if loaded_modules.get_module(&u.module_path).is_some() {
                  // Module already loaded, just update scope
                  loaded_scopes = loaded_modules.scopes();
                  global = loaded_scopes.global(&module_path).unwrap();
                } else {
                  let loaded = loaded_modules.clone();
                  let res = load_module_files(&u.module_path, loaded);
                  match res {
                    Ok(loaded) => {
                      if options.debug {
                        for module in loaded.modules() {
                          println!("Adding module {} to scope", module.path());
                        }
                      }
                      loaded_modules = loaded;
                      loaded_scopes = loaded_modules.scopes();
                      global = loaded_scopes.global(&module_path).unwrap();
                    }
                    Err(e) => eprintln!("loading error {e}"),
                  }
                }
              }
              ReplInput::Decls(decl) => {
                loaded_modules
                  .get_module_mut(&module_path)
                  .unwrap()
                  .add_decl(decl.clone());
                loaded_scopes = loaded_modules.scopes();
                global = loaded_scopes.global(&module_path).unwrap();
              }
            }
          }
        }
      }
      Err(ReadlineError::Interrupted) => {
        println!("CTRL-C");
        break;
      }
      Err(ReadlineError::Eof) => {
        println!("CTRL-D");
        break;
      }
      Err(err) => {
        println!("Error: {:?}", err);
        break;
      }
    }
  }
  rl.save_history("history.txt").map_err(|e| format!("{e}"))?;
  Ok(())
}

pub fn run(input: PathBuf, args: Vec<String>, options: EvalOptions) -> Result<(), String> {
  let path: ModulePath = input.into();
  let mut loaded = default_modules().map_err(|e| format!("{e}"))?;
  loaded = load_module_files(&path, loaded).map_err(|e| format!("{e}"))?;
  let module = loaded
    .get_module(&path)
    .ok_or_else(|| format!("Module {path} not loaded"))?;
  let loaded_scopes = loaded.scopes();
  let global = loaded_scopes.global(&path).expect("Module not loaded");
  if options.debug {
    println!("{global}");
  }
  let arg: Term = strings_to_list_term(args);

  let def = module
    .get_def(&mpt("main"))
    .ok_or("main not found")?
    .value();
  let input_term = if def.term.is_lam() {
    app(def.term.clone(), arg)
  } else {
    def.term.clone()
  };

  let (term, typ) = type_check(input_term, Hole, &global.scope())
    .map_err(|e| format!("{e}"))
    .inspect_err(|e| eprintln!("{e}"))?
    .to_tuple();
  println!("Eval type {typ}");
  let term = eval(term, &global.scope(), &options)
    .map_err(|e| format!("{e}"))
    .inspect_err(|e| eprintln!("{e}"))?;

  if options.debug {
    println!("Eval result {term}");
  }
  Ok(())
}

pub fn vec_fmt<T: Display>(v: &[T]) -> String {
  v.iter()
    .map(|t| format!("{t}"))
    .collect::<Vec<String>>()
    .join(", ")
}

enum TestResult {
  Pass,
  Fail,
  FailWithMessage(String),
}

fn detect_test_result(term: &Term) -> TestResult {
  match term {
    Term::Ctx { term, .. } => detect_test_result(term),
    Con(Constructor {
      name,
      typ_name,
      args,
      ..
    }) => {
      if typ_name == &mpt("Bool") {
        return if name == &id("true") {
          TestResult::Pass
        } else if name == &id("false") {
          TestResult::Fail
        } else {
          TestResult::FailWithMessage(format!("unexpected result: {term}"))
        };
      }
      if typ_name == &mpt("IO")
        && let Some(Some(inner)) = args.first()
      {
        return detect_test_result(inner);
      }
      if typ_name == &mpt("Result") {
        if name == &id("ok") {
          return TestResult::Pass;
        } else if name == &id("err") {
          if let Some(Some(msg_term)) = args.first() {
            let msg = extract_string_literal(msg_term);
            return TestResult::FailWithMessage(msg.unwrap_or_else(|| msg_term.to_string()));
          }
          return TestResult::Fail;
        }
      }
      TestResult::FailWithMessage(format!("unexpected result: {term}"))
    }
    _ => TestResult::FailWithMessage(format!("unexpected result: {term}")),
  }
}

fn extract_string_literal(term: &Term) -> Option<String> {
  match term {
    Term::Ctx { term, .. } => extract_string_literal(term),
    Term::Lit {
      value: crate::term::Literal::Str { value },
    } => Some(value.clone()),
    _ => None,
  }
}

pub fn run_tests(input: PathBuf, options: EvalOptions) -> Result<(), String> {
  let path: ModulePath = input.into();
  let mut loaded = default_modules().map_err(|e| format!("{e}"))?;
  let test_path = ModulePath::new(vec![id("std"), id("test")]);
  loaded = load_module_files(&test_path, loaded).map_err(|e| format!("{e}"))?;
  loaded = load_module_files(&path, loaded).map_err(|e| format!("{e}"))?;
  let module = loaded
    .get_module(&path)
    .ok_or_else(|| format!("Module {path} not loaded"))?;
  let loaded_scopes = loaded.scopes();
  let global = loaded_scopes.global(&path).expect("Module not loaded");
  if options.debug {
    println!("{global}");
  }

  let test_defs: Vec<_> = module
    .defs()
    .into_iter()
    .filter(|ctx| ctx.value().has_test_attr())
    .collect();

  if test_defs.is_empty() {
    return Err("No tests found".to_string());
  }

  let mut passed = 0;
  let mut failed = 0;
  let mut failures: Vec<(String, String)> = Vec::new();

  for ctx in &test_defs {
    let def = ctx.value();
    let name = def.name.to_string();
    let term = def.term.clone();

    let (term, typ) = match type_check(term, Hole, &global.scope()) {
      Ok(tt) => tt.to_tuple(),
      Err(e) => {
        failed += 1;
        failures.push((name.clone(), format!("type error: {e}")));
        continue;
      }
    };

    if options.debug {
      println!("test {name} : {typ}");
    }

    let result = match eval(term, &global.scope(), &options) {
      Ok(t) => t,
      Err(e) => {
        failed += 1;
        failures.push((name.clone(), format!("eval error: {e}")));
        failed += 1;
        failures.push((name.clone(), format!("eval error: {e}")));
        failed += 1;
        failures.push((name.clone(), format!("eval error: {e}")));
        continue;
      }
    };

    if options.debug {
      println!("  eval: {result}");
    }

    match detect_test_result(&result) {
      TestResult::Pass => {
        passed += 1;
        println!("PASS {name}");
      }
      TestResult::Fail => {
        failed += 1;
        println!("FAIL {name}");
      }
      TestResult::FailWithMessage(msg) => {
        failed += 1;
        println!("FAIL {name}: {msg}");
        failures.push((name.clone(), msg));
      }
    }
  }

  let total = passed + failed;
  println!("{passed}/{total} tests passed");

  if failed > 0 {
    for (name, msg) in &failures {
      eprintln!("FAIL {name}: {msg}");
    }
    Err(format!("{failed} test(s) failed"))
  } else {
    Ok(())
  }
}
