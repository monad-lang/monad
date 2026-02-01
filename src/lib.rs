use rustyline::DefaultEditor;
use rustyline::error::ReadlineError;
use std::collections::{BTreeMap, HashSet};
use std::fmt::Display;
use std::hash::{BuildHasherDefault, DefaultHasher, Hash};
use std::path::PathBuf;

use crate::eval::r#type::type_check;
use crate::eval::{EvalOptions, eval};
use crate::parser::{ReplInput, repl_parser};
use crate::term::Term::Hole;
use crate::term::module::{default_modules, load_module_files, module};
use crate::term::{Decl, Term, app, to_list_term};
use crate::term::{ModulePath, mpt};

pub mod eval;
pub mod parser;
pub mod term;

pub type Set<T> = HashSet<T, BuildHasherDefault<DefaultHasher>>;
pub fn empty_set<T: Eq + Hash>() -> Set<T> {
  let set = HashSet::with_hasher(BuildHasherDefault::new());
  set
}

pub fn set_of<T: Eq + Hash>(vals: impl Iterator<Item = T>) -> Set<T> {
  let mut set = empty_set();
  for value in vals {
    set.insert(value);
  }
  set
}

pub type Map<K, V> = BTreeMap<K, V>;

pub fn repl(options: EvalOptions) -> Result<(), String> {
  let mut rl = DefaultEditor::new().map_err(|e| format!("{e}"))?;

  if rl.load_history("history.txt").is_err() {
    println!("No previous history.");
  }
  let mut loaded_modules = default_modules().map_err(|e| format!("{e}"))?;
  let module_path = ModulePath::top("'repl");
  let module = module(module_path.clone(), vec![]);
  loaded_modules.add_module(module);
  let mut global = loaded_modules.global(&module_path).unwrap();
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
                    global = loaded_modules.global(&module_path).unwrap();
                  }
                  Err(e) => eprintln!("loading error {e}"),
                }
              }
              ReplInput::Decls(decl) => {
                loaded_modules
                  .get_module_mut(&module_path)
                  .unwrap()
                  .add_decl(decl.clone());
                global = loaded_modules.global(&module_path).unwrap();
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
  let global = loaded.global(&path).expect("Module not loaded");
  if options.debug {
    println!("{global}");
  }
  let arg: Term = to_list_term(args);

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

pub fn vec_fmt<T: Display>(v: &Vec<T>) -> String {
  v.iter()
    .map(|t| format!("{t}"))
    .collect::<Vec<String>>()
    .join(", ")
}
