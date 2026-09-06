//! End-to-end test for Phase 0 of
//! `plans/implementations/core-term-closure-evaluator.md`: whole-program
//! `CoreTerm` retention via `check_all_modules_capturing_core`.
//!
//! Exercises the exact scenario that motivated the design: two
//! inductives sharing a constructor literally named `cons` (mirroring
//! `init/prelude.mo`'s real `List`/`Vec`), each matched on unqualified —
//! so re-deriving "which inductive is this match on" from constructor
//! names alone (post-hoc, from the final `CoreTerm`) is genuinely
//! ambiguous. This test checks that the resolved inductive `Atom`,
//! captured at checker time, actually disambiguates the two.

use monad_core::core_check_module::check_all_modules_capturing_core;
use monad_core::core_ir::CoreIr;
use monad_core::lower_core_ir::{GlobalDef, lower_program};
use monad_core::term::Decl;
use monad_core::term::module::{default_modules, load_decls_from_text_with_path};
use monad_core::term::{ModulePath, SourceContext, mpt};

/// `check_all_modules_capturing_core` only captures `Decl::Type`/`Match`
/// resolutions for whichever modules' raw decls are explicitly passed in
/// — a program that `use`s `init` needs `init/prelude.mo`'s own
/// inductives (`Bool`, `BEq`, ...) captured too, or lowering anything
/// that touches them (any `if`, any dictionary-backed operator) fails
/// with `UnresolvedMatch`/`UnknownInductive`. `'prelude` is loaded from
/// embedded source the same way `default_modules()` itself loads it
/// (`init_module`, `term/module.rs`) — re-parsed here fresh since
/// `default_modules()`'s own copy is already checked/raised `Term`, not
/// the raw `Decl`s this driver needs as input.
fn prelude_decls() -> Vec<SourceContext<Decl>> {
  let text = include_str!("../../init/prelude.mo");
  load_decls_from_text_with_path(text, &Default::default()).expect("parse init/prelude.mo")
}

// `Stack`/`Queue` intentionally both declare a bare `cons` constructor —
// mirrors `init/prelude.mo`'s real `List`/`Vec`, which do the same thing
// (see the plan's Phase 0 section) — self-contained here so this test
// doesn't depend on the exact current shape of the real prelude types.
const SOURCE: &str = r#"
use init

type Stack {
    cons (head : I64) (tail : Stack),
    empty
}

type Queue {
    cons (head : I64) (tail : Queue),
    nil
}

instance BEq I64 {
    def beq (a : I64) (b : I64) : Bool := a == b
}

def match_stack_cons (xs : Stack) : I64 :=
    match xs {
        cons x _ => x,
        empty => 0
    }

def match_queue_cons (xs : Queue) : I64 :=
    match xs {
        cons x _ => x,
        nil => 0
    }

def five : I64 := 5
"#;

#[test]
fn phase0_captures_whole_program_core_terms() {
  let loaded = default_modules().expect("default_modules");
  let path = ModulePath::top("'phase0test");
  let ctx = Default::default();
  let decls = load_decls_from_text_with_path(SOURCE, &ctx).expect("parse");

  let program = check_all_modules_capturing_core(&[(path.clone(), decls)], &loaded)
    .expect("check_all_modules_capturing_core");

  // --- defs: an ordinary top-level def is captured under its own path
  //     (a bare, unqualified name — module qualification isn't baked
  //     into `Def.name` at check time in this codebase) ---
  let five_path = mpt("five");
  assert!(
    program.defs.contains_key(&five_path),
    "expected a captured def at {five_path}, got keys: {:?}",
    program.defs.keys().collect::<Vec<_>>()
  );

  // --- inductives: Stack/Queue are registered with their constructors
  //     in declaration order (order == tag), both sharing a `cons` name ---
  let stack_path = mpt("Stack");
  let stack_info = program.inductives.get(&stack_path).unwrap_or_else(|| {
    panic!(
      "expected Stack in inductives, got: {:?}",
      program.inductives.keys().collect::<Vec<_>>()
    )
  });
  assert!(
    stack_info
      .constructors
      .iter()
      .any(|c| c.name.as_str() == "cons" && c.arity == 2),
    "Stack should have a 2-arity cons constructor, got {:?}",
    stack_info.constructors
  );

  let queue_path = mpt("Queue");
  let queue_info = program.inductives.get(&queue_path).unwrap_or_else(|| {
    panic!(
      "expected Queue in inductives, got: {:?}",
      program.inductives.keys().collect::<Vec<_>>()
    )
  });
  assert!(
    queue_info
      .constructors
      .iter()
      .any(|c| c.name.as_str() == "cons" && c.arity == 2),
    "Queue should have a 2-arity cons constructor, got {:?}",
    queue_info.constructors
  );

  // --- match_resolutions: the two `cons` matches resolve to DIFFERENT
  //     atoms, disambiguating Stack from Queue despite the shared name —
  //     each def's own resolutions are recorded under its own path, in
  //     visitation order (see `CoreProgram::match_resolutions`'s doc
  //     comment for why this isn't content-keyed) ---
  let stack_resolutions = program
    .match_resolutions
    .get(&mpt("match_stack_cons"))
    .expect("expected captured match resolutions for match_stack_cons");
  assert_eq!(
    stack_resolutions.len(),
    1,
    "one match expression in the body"
  );
  let (stack_case_names, stack_atom) = &stack_resolutions[0];
  assert!(stack_case_names.iter().any(|n| n.as_str() == "empty"));

  let queue_resolutions = program
    .match_resolutions
    .get(&mpt("match_queue_cons"))
    .expect("expected captured match resolutions for match_queue_cons");
  assert_eq!(
    queue_resolutions.len(),
    1,
    "one match expression in the body"
  );
  let (queue_case_names, queue_atom) = &queue_resolutions[0];
  assert!(queue_case_names.iter().any(|n| n.as_str() == "nil"));

  assert_ne!(
    stack_atom, queue_atom,
    "Stack's and Queue's `cons` matches must resolve to different inductive atoms"
  );

  // --- instances: BEq I64's dictionary shape is recorded, and its one
  //     method (`beq`) is independently present in `defs` under an
  //     instance-qualified path ---
  let (instance_path, info) = program
    .instances
    .iter()
    .find(|(p, _)| p.to_string().contains("BEq"))
    .unwrap_or_else(|| {
      panic!(
        "expected a BEq instance, got: {:?}",
        program.instances.keys().collect::<Vec<_>>()
      )
    });
  assert_eq!(info.method_paths.len(), 1, "BEq has exactly one method");
  let method_path = &info.method_paths[0];
  assert!(
    program.defs.contains_key(method_path),
    "instance {instance_path}'s method path {method_path} should be captured in defs, got keys: {:?}",
    program.defs.keys().collect::<Vec<_>>()
  );
}

/// End-to-end test for Phase 2 (`lower_core_ir::lower_program`), against
/// the exact same captured `CoreProgram` as the Phase 0 test above.
#[test]
fn phase2_lowers_whole_program_to_ir() {
  let loaded = default_modules().expect("default_modules");
  let path = ModulePath::top("'phase2test");
  let ctx = Default::default();
  let decls = load_decls_from_text_with_path(SOURCE, &ctx).expect("parse");
  let prelude_path = ModulePath::top("'prelude");
  let program = check_all_modules_capturing_core(
    &[(prelude_path, prelude_decls()), (path.clone(), decls)],
    &loaded,
  )
  .expect("check_all_modules_capturing_core");

  let lowered = lower_program(&program).expect("lower_program");

  // Every captured def got its own global slot with a real lowered body.
  assert!(
    !lowered.globals.is_empty(),
    "expected at least one global slot"
  );
  let def_bodies: Vec<&CoreIr> = lowered
    .globals
    .iter()
    .filter_map(|g| match g {
      GlobalDef::Def(ir) | GlobalDef::Effect(ir) => Some(ir.as_ref()),
      GlobalDef::Constructor { .. } | GlobalDef::Native { .. } | GlobalDef::Unresolved(_) => None,
    })
    .collect();
  assert!(
    !def_bodies.is_empty(),
    "expected at least one Def-kind global slot"
  );

  // `five`'s body lowers to a plain literal (no Local/Global references
  // at all -- it's a closed, zero-argument value).
  let has_five_literal = def_bodies
    .iter()
    .any(|ir| matches!(ir, CoreIr::Lit(monad_core::core_ir::IrLit::Num(5, _))));
  assert!(
    has_five_literal,
    "expected `five`'s lowered body to be the literal 5, bodies: {:?}",
    def_bodies
      .iter()
      .map(|ir| ir.to_string())
      .collect::<Vec<_>>()
  );

  // `match_stack_cons`/`match_queue_cons` each lower to a Lam wrapping a
  // 2-arm Match whose first arm binds 2 fields (`cons x _ => x`) and
  // second binds none (`empty`/`nil => 0`) -- matched by exact shape
  // (not just count) since `init/prelude.mo`'s own defs (also lowered
  // here) contain plenty of other 2-arm matches too.
  let match_bodies: Vec<&CoreIr> = def_bodies
    .iter()
    .filter(|ir| match ir {
      CoreIr::Lam { body } => match body.as_ref() {
        CoreIr::Match { arms, .. } => {
          arms.len() == 2 && arms[0].bind_count == 2 && arms[1].bind_count == 0
        }
        _ => false,
      },
      _ => false,
    })
    .copied()
    .collect();
  // >= 2, not == 2: `CoreProgram.defs` now stores every def under BOTH
  // its bare AND module-qualified path (`insert_checked_def`,
  // core_check_module.rs -- needed so a same-module self-reference and
  // a cross-module reference to a non-colliding name both resolve),
  // so `match_stack_cons`/`match_queue_cons` each get lowered (and
  // counted here) once per key -- redundant work, not a correctness
  // issue, and not this test's own concern (shape, not count).
  assert!(
    match_bodies.len() >= 2,
    "expected at least 2 lowered defs shaped like match_stack_cons/match_queue_cons, got: {:?}",
    def_bodies
      .iter()
      .map(|ir| ir.to_string())
      .collect::<Vec<_>>()
  );

  // The BEq I64 instance's dictionary slot assembles to a single-field
  // Con (tag 0, one method) whose sole arg is a Global reference -- not
  // an inlined copy of the method's body.
  let dict_cons: Vec<&CoreIr> = lowered
    .globals
    .iter()
    .filter_map(|g| match g {
      GlobalDef::Def(ir) => match ir.as_ref() {
        CoreIr::Con { tag: 0, args, .. } if args.len() == 1 => Some(ir.as_ref()),
        _ => None,
      },
      _ => None,
    })
    .collect();
  assert!(
    !dict_cons.is_empty(),
    "expected the BEq I64 dictionary to lower to a 1-field Con, globals: {:?}",
    lowered
      .globals
      .iter()
      .map(|g| match g {
        GlobalDef::Def(ir) => ir.to_string(),
        GlobalDef::Effect(ir) => format!("<effect {ir}>"),
        GlobalDef::Constructor { tag, arity } => format!("<ctor #{tag}/{arity}>"),
        GlobalDef::Native { native_id, arity } => format!("<native #{native_id}/{arity}>"),
        GlobalDef::Unresolved(path) => format!("<unresolved {path}>"),
      })
      .collect::<Vec<_>>()
  );
  let CoreIr::Con { args, .. } = dict_cons[0] else {
    unreachable!()
  };
  assert!(
    matches!(args[0].as_ref(), CoreIr::Global(_)),
    "dictionary field should be a Global reference (shared/memoized method), got {}",
    args[0]
  );

  // The BEq I64 instance's `beq` method body (`a == b`) itself uses a
  // class method (`==`, dictionary-projected via `project_dict_field`)
  // -- confirms the fix for the dictionary-projection Match capture gap
  // (project_dict_field's synthesized Match nodes run inside
  // desugar_struct_literals, *after* check/infer already completed, so
  // the original check/infer-only capture never saw them). `beq`'s own
  // method path must NOT appear in `skipped`.
  let (_, beq_info) = program
    .instances
    .iter()
    .find(|(p, _)| p.to_string().contains("BEq"))
    .expect("expected a BEq instance");
  let beq_method_path = &beq_info.method_paths[0];
  assert!(
    !lowered.skipped.iter().any(|(p, _)| p == beq_method_path),
    "expected beq's dictionary-backed `==` body to lower successfully, but it was skipped: {:?}",
    lowered.skipped
  );
}
