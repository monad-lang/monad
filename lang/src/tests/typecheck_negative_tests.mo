/// Negative type-checking pins: illegal programs the checker must REJECT.
///
/// They go through `check_file_cached_from_source_ranged`, which runs the
/// same elaboration and the same per-declaration walk `monad check` uses,
/// with the ambient prelude/init/std tier included. That matters more than
/// the convenience: `typecheck_source` (in `typecheck_examples_tests.mo`)
/// builds a prelude-less synthetic scope, and a pin written against it can
/// be green while `monad check` accepts the identical source -- see
/// `implementations/match-arm-conversion-vacuous-in-check.md`. Every
/// rejection pin here is paired with an ACCEPTANCE source (`accepted`)
/// covering the same callees and types, so a rule that rejects everything,
/// or a fixture whose names never resolve, cannot pass.
///
/// Diagnostic text is asserted, not merely its presence: a pin that only
/// counts errors would go green on an unrelated unknown-name failure.
use lib::module {
    Diagnostic, check_file_cached_from_source_ranged, diagnostic_message,
    module_info_cache_empty, ranged_file_diagnostics,
}
use std::process {exec_cmd, process_id}
use std::test {Test.write_fixture}
open IO {println}

// --- Rendering diagnostics -------------------------------------------------
// Field reads are routed through typed accessors rather than written inline
// in a `#[test]` def: a test def that touches a struct field is the recorded
// self-hosted codegen hazard.

#[terminating]
def messages_of (ds : List Diagnostic) : List String :=
    match ds {
        List.empty => List.empty,
        List.cons d rest => List.cons (diagnostic_message d) (messages_of rest),
    }

#[terminating]
def joined (msgs : List String) : String :=
    match msgs {
        List.empty => "",
        List.cons m rest => String.concat m (String.concat "\n  " (joined rest)),
    }

/// The diagnostic rendered `... in <name>`, if the checker reported one for
/// that declaration.
#[terminating]
def message_named (name : String) (msgs : List String) : Option String :=
    match msgs {
        List.empty => Option.none,
        List.cons m rest =>
            if String.contains m (String.concat " in " name)
            then Option.some m
            else message_named name rest,
    }

// --- Fixtures --------------------------------------------------------------
// The source is checked from a BUFFER, but it must also exist on disk: the
// loader resolves the target module through `resolve_module_file`
// (`lang/src/module.mo`) before it ever looks at the supplied text, so a path
// nothing resolves to reports `Failed to load` instead of type-checking --
// which a count-only pin would read as success. Same shape as
// `decl_range_tests.mo`'s fixture. The `process_id` suffix keeps the sweep's
// parallel shards apart.
def probe_dir : String := "/tmp/monad_typecheck_negative_" ++ I64.to_string process_id

def probe_path : String := probe_dir ++ "/probe.mo"

#[partial]
def diagnostics_for (src : String) : IO (List String) := do {
    let _mk <- exec_cmd "mkdir" ["-p", probe_dir];
    let _w <- Test.write_fixture (Path.path probe_path) src;
    let checked <- check_file_cached_from_source_ranged module_info_cache_empty probe_path src false;
    return (messages_of (ranged_file_diagnostics checked))
}

/// Does checking `src` report a diagnostic naming `name` whose text contains
/// `needle`?
#[partial]
def rejected_with (name : String) (needle : String) (src : String) : IO Bool := do {
    let msgs <- diagnostics_for src;
    match message_named name msgs {
        Option.none => do {
            println ("MISSING: expected a diagnostic naming " ++ name ++ "; got:\n  " ++ joined msgs);
            return false
        },
        Option.some m =>
            if String.contains m needle
            then return true
            else do {
                println ("WRONG DIAGNOSTIC for " ++ name ++ " (expected text containing \"" ++ needle ++ "\")");
                return false
            },
    }
}

/// The control half: a well-typed source must produce NO diagnostics.
#[partial]
def accepted (src : String) : IO Bool := do {
    let msgs <- diagnostics_for src;
    match msgs {
        List.empty => return true,
        _ => do {
            println ("UNEXPECTED diagnostics:\n  " ++ joined msgs);
            return false
        },
    }
}

def mismatch : String := "type mismatch"

// --- Call arguments against the callee's Pi domain -------------------------

/// First-order: `style` wants `List String`, the argument is a `String`.
/// The declaration is deliberately the PARTIAL APPLICATION's own type
/// (`String -> I64`), so the def-boundary comparison agrees and only the
/// argument rule can reject this.
def first_order_source : String :=
    "def style (attrs : List String) (content : String) : I64 := 0\ndef css : String := \"x\"\ndef arg_first_order : String -> I64 := style css\n"

/// A literal argument: `take_i64` wants `I64`, the argument is a `String`.
def literal_arg_source : String :=
    "def take_i64 (x : I64) : I64 := x\ndef arg_literal : I64 := take_i64 \"s\"\n"

/// Higher-order: `needs` wants `I64 -> Msg`, the argument is a nullary
/// constructor value of type `Msg`. The call's own type is `Msg`, equal to
/// the declaration, so the def boundary cannot see it -- this is the shape
/// that compiled a garbage closure and overflowed the wasm stack.
def second_order_source : String :=
    "type Msg { started }\ndef needs (f : I64 -> Msg) : Msg := f 0i64\ndef arg_second_order : Msg := needs Msg.started\n"

/// A local FUNCTION VALUE's parameter: no def signature is involved, so
/// this is the ordinary application path's own check (a def call resolves
/// through the signature-driven path and never reaches it).
def local_apply_source : String :=
    "def danger (pick : String -> I64) : I64 := pick 1i64\n"

#[test]
def test_a_first_order_argument_of_the_wrong_type_is_rejected : IO Bool :=
    rejected_with "arg_first_order" mismatch first_order_source

#[test]
def test_an_argument_to_a_local_function_value_is_rejected : IO Bool :=
    rejected_with "danger" mismatch local_apply_source

#[test]
def test_a_literal_argument_of_the_wrong_type_is_rejected : IO Bool :=
    rejected_with "arg_literal" mismatch literal_arg_source

#[test]
def test_a_higher_order_argument_of_the_wrong_type_is_rejected : IO Bool :=
    rejected_with "arg_second_order" mismatch second_order_source

#[test]
def test_correct_arguments_and_guarded_shapes_are_accepted : IO Bool :=
    accepted (
        "def style (attrs : List String) (content : String) : I64 := 0\n"
        ++ "def attrs0 : List String := List.empty\n"
        ++ "def arg_ok : I64 := style attrs0 \"b\"\n"
        ++ "type Msg { started }\n"
        ++ "def needs (f : I64 -> Msg) : Msg := f 0i64\n"
        ++ "def mk_msg (x : I64) : Msg := Msg.started\n"
        ++ "def arg_ok2 : Msg := needs mk_msg\n"
        // an uninstantiated type variable in the parameter must stay
        // permissive (the guard `body_type_error` documents)
        ++ "def len {A : Type} (xs : List A) : I64 := 0\n"
        ++ "def arg_generic : I64 := len [1, 2]\n"
        // a do-bind's continuation lambda carries a hole binder
        ++ "def m : IO I64 := IO.pure 1\n"
        ++ "def arg_do : IO I64 := do { let x <- m; return x }\n"
        // a local function value applied at its own domain
        ++ "def safe (pick : String -> I64) : I64 := pick \"s\"\n"
        // a constructor WITH fields passed as a function value: the
        // checker types a constructor reference as its owning type, so
        // this must stay accepted until constructor-as-value typing lands
        ++ "type Box { box (value : I64) }\n"
        ++ "def use_box (f : I64 -> Box) : Box := f 1i64\n"
        ++ "def box_ok : Box := use_box Box.box\n")

// --- Distinct String newtypes: `Path` is not a `String` --------------------
//
// `plans/implementations/2026-11-14-infix-concat-accepts-a-path.md`. `++` is
// `Append.append` (init/src/prelude.mo), a class method, so the operand check
// has to read the CLASS's declared parameter solved by the arguments already
// applied; before that, `"at " ++ p` checked cleanly and compiled a `Path`
// into the `String` slot. The argument shapes below are the same rule through
// a def call and were the docgen call that segfaulted the site build.

def concat_path_operand_source : String :=
    "def show_path (p : Path) : String := \"at \" ++ p\n"

def concat_path_operand_left_source : String :=
    "def show_path_left (p : Path) : String := p ++ \"at \"\n"

def append_path_operand_source : String :=
    "def append_path (p : Path) : String := Append.append \"at \" p\n"

def concat_path_operand_ok_source : String :=
    "def show_path_ok (p : Path) : String := \"at \" ++ Path.to_string p\n"
    ++ "def show_path_right_ok (p : Path) : String := Path.to_string p ++ \"at \"\n"

#[test]
def test_a_path_operand_of_concat_is_rejected : IO Bool :=
    rejected_with "show_path" mismatch concat_path_operand_source

#[test]
def test_a_path_first_operand_rejects_a_string_second : IO Bool :=
    rejected_with "show_path_left" mismatch concat_path_operand_left_source

#[test]
def test_a_path_operand_of_append_is_rejected : IO Bool :=
    rejected_with "append_path" mismatch append_path_operand_source

#[test]
def test_rendering_the_path_before_concatenating_is_accepted : IO Bool :=
    accepted concat_path_operand_ok_source

/// The class-method argument rule must not fire where the declared parameter
/// is still a class variable: `Monad.bind`'s `A -> M B`, a user generic
/// helper, `Append.append` at its own type and `HAdd`'s two-parameter `+`
/// are all accepted -- the shapes every do-block in the corpus and
/// `motes/oak/src/tests/html_t_tests.mo` depend on.
def class_method_guards_ok_source : String :=
    "def append_ok (s : String) : String := Append.append \"a\" s\n"
    ++ "def bind_ok {A B : Type} (m : IO A) (f : A -> IO B) : IO B := Monad.bind m f\n"
    ++ "def do_ok : IO I64 := do { let x <- IO.pure 1; return x }\n"
    ++ "def add_ok (a b : I64) : I64 := a + b\n"

#[test]
def test_class_method_arguments_at_a_class_variable_are_accepted : IO Bool :=
    accepted class_method_guards_ok_source

def path_argument_source : String :=
    "def take_path (dir : Path) : String := \"x\"\n"
    ++ "def path_argument (p : Path) : String := take_path (Path.to_string p)\n"

def path_argument_ok_source : String :=
    "def take_path_ok (dir : Path) : String := \"x\"\n"
    ++ "def path_argument_ok (p : Path) : String := take_path_ok p\n"

#[test]
def test_a_string_argument_to_a_path_parameter_is_rejected : IO Bool :=
    rejected_with "path_argument" mismatch path_argument_source

#[test]
def test_a_path_argument_to_a_path_parameter_is_accepted : IO Bool :=
    accepted path_argument_ok_source

def string_beq_path_source : String :=
    "def beq_path (p : Path) (s : String) : Bool := String.beq p s\n"

def string_length_path_source : String :=
    "def len_path (p : Path) : I64 := String.length p\n"

def string_native_path_ok_source : String :=
    "def beq_path_ok (p : Path) (s : String) : Bool := String.beq (Path.to_string p) s\n"
    ++ "def len_path_ok (p : Path) : I64 := String.length (Path.to_string p)\n"

#[test]
def test_a_path_argument_to_string_beq_is_rejected : IO Bool :=
    rejected_with "beq_path" mismatch string_beq_path_source

#[test]
def test_a_path_argument_to_string_length_is_rejected : IO Bool :=
    rejected_with "len_path" mismatch string_length_path_source

#[test]
def test_the_rendered_string_native_twins_are_accepted : IO Bool :=
    accepted string_native_path_ok_source

/// The exact docgen shape, across a module boundary: `manifest_at` takes a
/// `Path`, and the argument is `Path.to_string mote_dir`. This compiled and
/// then miscompiled the site binary (exit 139) before the caller was fixed.
def manifest_at_path_source : String :=
    "use lang::mote {Mote.manifest_at}\n"
    ++ "def probe_manifest (mote_dir : Path) : IO String := do {\n"
    ++ "    let _manifest <- Mote.manifest_at (Path.to_string mote_dir);\n"
    ++ "    return \"x\"\n"
    ++ "}\n"

def manifest_at_path_ok_source : String :=
    "use lang::mote {Mote.manifest_at}\n"
    ++ "def probe_manifest_ok (mote_dir : Path) : IO String := do {\n"
    ++ "    let _manifest <- Mote.manifest_at mote_dir;\n"
    ++ "    return \"x\"\n"
    ++ "}\n"

#[test]
def test_a_string_argument_to_manifest_at_is_rejected : IO Bool :=
    rejected_with "probe_manifest" mismatch manifest_at_path_source

#[test]
def test_a_path_argument_to_manifest_at_is_accepted : IO Bool :=
    accepted manifest_at_path_ok_source

// --- `if` / `else` arms ----------------------------------------------------

/// The then-arm is `IO I64` and the else-arm `IO String`; the declaration
/// equals the THEN type, so only the branch comparison can reject this.
///
/// A CONCRETE mismatch on purpose. An arm whose type still carries an
/// unsolved type variable (`IO.pure (Result.ok Unit.unit)` infers
/// `IO (Result _ _)`) is skipped by `body_type_error`'s typevar guard --
/// pinned as accepted below, since `docs/src/bootstrap-host.md` states it.
def if_source : String :=
    "def if_branches : IO I64 := if true then IO.pure 0 else IO.pure \"s\"\n"

#[test]
def test_if_arms_of_different_types_are_rejected : IO Bool :=
    rejected_with "if_branches" mismatch if_source

#[test]
def test_if_arms_of_the_same_type_are_accepted : IO Bool :=
    accepted "def if_ok : IO I64 := if true then IO.pure 0 else IO.pure 1\n"

/// The typevar guard's permissive half. Deleting the guard must show up
/// here, not as a silent divergence from the Rust host.
#[test]
def test_if_arms_whose_type_still_carries_a_type_variable_are_accepted : IO Bool :=
    accepted "def if_hole_arm : IO I64 := if true then IO.pure 0 else IO.pure (Result.ok Unit.unit)\n"

// --- Struct literals and updates -------------------------------------------

def struct_unknown_source : String :=
    "struct P { x : I64, y : I64 }\ndef struct_unknown : P := { x := 1, y := 2, nosuch := 3 }\n"

def struct_short_source : String :=
    "struct P { x : I64, y : I64 }\ndef struct_short : P := { x := 1 }\n"

def struct_update_source : String :=
    "struct P { x : I64, y : I64 }\ndef struct_update_unknown (p : P) : P := { p with nosuch := 3 }\n"

#[test]
def test_a_struct_literal_with_an_unknown_field_is_rejected : IO Bool :=
    rejected_with "struct_unknown" "unknown field `nosuch`" struct_unknown_source

#[test]
def test_a_struct_literal_missing_a_required_field_is_rejected : IO Bool :=
    rejected_with "struct_short" "missing required field `y`" struct_short_source

#[test]
def test_a_struct_update_with_an_unknown_field_is_rejected : IO Bool :=
    rejected_with "struct_update_unknown" "unknown field `nosuch`" struct_update_source

#[test]
def test_complete_literals_and_defaulted_omissions_are_accepted : IO Bool :=
    accepted (
        "struct P { x : I64, y : I64 }\n"
        ++ "def complete : P := { x := 1, y := 2 }\n"
        ++ "struct Q { x : I64, y : I64 := 7 }\n"
        ++ "def defaulted : Q := { x := 1 }\n"
        ++ "def updated (p : P) : P := { p with y := 3 }\n")

// --- The affine rule on dimension binders --------------------------------
//
// The only harness that runs the REAL `monad check` pipeline over
// `em.target_decls`, which is where the affine walk sees lowered source --
// a dimension binder's type is the reference `Cubical.I`, not a cubical
// node. `instance Copy Cubical.I` (`init/src/copy.mo`) is admissible only
// because `filter_unknown_types` (`lang/src/scope.mo`) stopped recovering a
// QUALIFIED name as an unquantified type variable, so these two pins are the
// driver-level before/after for that rule.

#[test]
def test_a_dimension_used_twice_is_accepted : IO Bool :=
    accepted "def dup_i (i : Cubical.I) : Pair Cubical.I Cubical.I := Pair.pair i i\n"

/// ... and the licence is specific to the interval: an ordinary affine type
/// used twice is still an error. Without this the pin above would also pass
/// if the rule had simply stopped enforcing anything.
#[test]
def test_a_non_copy_type_used_twice_is_still_rejected : IO Bool :=
    rejected_with "dup_nocopy" "is moved 2 times"
        ("type NoCopy { mk }\n"
            ++ "def dup_nocopy (x : NoCopy) : Pair NoCopy NoCopy := Pair.pair x x\n")

// --- The `#[proof]` def exemption ---------------------------------------
//
// A proof def's result is erased, so its body is proof code and may use any
// binder freely. This is what licenses a contractibility proof's centre,
// `Sigma.dpair b (refl b)`, which duplicates a DATA value `b : A` that no
// `Copy` instance can cover (measured 2026-11-05).

#[test]
def test_a_proof_def_may_duplicate_a_value : IO Bool :=
    accepted
        ("type NoCopyP { mk }\n"
            ++ "#[proof]\n"
            ++ "def dup_proof (x : NoCopyP) : Pair NoCopyP NoCopyP := Pair.pair x x\n")

/// ... and the exemption is opt-in: the SAME body without the marker is still
/// an error, so the rule did not become a blanket switch.
#[test]
def test_the_same_duplication_without_the_proof_marker_is_rejected : IO Bool :=
    rejected_with "dup_plain" "is moved 2 times"
        ("type NoCopyP { mk }\n"
            ++ "def dup_plain (x : NoCopyP) : Pair NoCopyP NoCopyP := Pair.pair x x\n")

// --- The `#[allow_non_affine]` opt-out -----------------------------------
//
// The migration escape hatch, on the same body shape as the `#[proof]` pins:
// the attribute on the DEF exempts it, and the unmarked twin above
// (`dup_plain`) is still rejected, so this cannot pass as a blanket switch.

#[test]
def test_allow_non_affine_exempts_a_def : IO Bool :=
    accepted
        ("type NoCopyA { mk }\n"
            ++ "#[allow_non_affine \"test: the opt-out must compile\"]\n"
            ++ "def dup_allowed (x : NoCopyA) : Pair NoCopyA NoCopyA := Pair.pair x x\n")

// --- ISSUE-8: dependent types across a binder ------------------------------
//
// `expected (B a0), found (B a0)`: two producers placed a type written in the
// caller's context under a binder without shifting it. The redex
// `(fn (x : B a0) => x) b0` (and every annotated `let`, which desugars to it)
// went through `type_check_app_ordinary`'s synthesized Pi; a call to a def
// whose return mentions its own parameters went through `instantiate_ret`.
// Each acceptance pin has a rejection twin that differs only in the index, so
// "accept everything" cannot pass.

def dep_id_source : String :=
    "def idb {A : Type} (B : A -> Type) (a0 : A) (y : B a0) : B a0 := y\n"

#[test]
def test_an_annotated_let_of_a_dependent_type_is_accepted : IO Bool :=
    accepted
        "def d_let {A : Type} (B : A -> Type) (a0 : A) (b0 : B a0) : B a0 :=\n    let x : B a0 := b0 in x\n"

#[test]
def test_a_dependent_beta_redex_is_accepted : IO Bool :=
    accepted
        "def d_redex {A : Type} (B : A -> Type) (a0 : A) (b0 : B a0) : B a0 :=\n    (fn (x : B a0) => x) b0\n"

#[test]
def test_a_let_at_the_wrong_index_is_rejected : IO Bool :=
    rejected_with "d_let_wrong" mismatch
        "def d_let_wrong {A : Type} (B : A -> Type) (a0 : A) (a1 : A) (b0 : B a0) : B a1 :=\n    let x : B a0 := b0 in x\n"

#[test]
def test_a_call_with_a_dependent_return_is_accepted : IO Bool :=
    accepted
        (dep_id_source
            ++ "def d_call {A : Type} (B : A -> Type) (a0 : A) (b0 : B a0) : B a0 := idb B a0 b0\n")

#[test]
def test_a_call_inside_a_let_with_a_dependent_return_is_accepted : IO Bool :=
    accepted
        (dep_id_source
            ++ "def d_let_call {A : Type} (B : A -> Type) (a0 : A) (b0 : B a0) : B a0 :=\n    let x : B a0 := b0 in idb B a0 x\n")

#[test]
def test_a_call_at_the_wrong_index_is_rejected : IO Bool :=
    rejected_with "d_call_wrong" mismatch
        (dep_id_source
            ++ "def d_call_wrong {A : Type} (B : A -> Type) (a0 : A) (a1 : A) (b0 : B a0) : B a1 := idb B a0 b0\n")

// --- Path boundaries through a constructor application --------------------
//
// `path_pair`'s remaining failure (after ISSUE-8) is not a binder-depth bug:
// even a CONSTANT path `fn i => Pair.pair a0 b0` failed its i0 boundary,
// because the boundary `unify` saw the checked body's constructor spelling
// against the endpoint's. The twin swaps the endpoint's components, so a
// boundary rule that accepts everything cannot pass.

#[test]
def test_a_constant_constructor_path_meets_its_boundary : IO Bool :=
    accepted
        "def pc_const {A : Type} {B : Type} (a0 : A) (b0 : B) :\n    Cubical.PathP (fn (i : Cubical.I) => Pair A B) (Pair.pair a0 b0) (Pair.pair a0 b0) :=\n    fn (i : Cubical.I) => Pair.pair a0 b0\n"

#[test]
def test_a_constructor_path_with_the_wrong_endpoint_is_rejected : IO Bool :=
    rejected_with "pc_wrong" "i0 boundary"
        "def pc_wrong {A : Type} (a0 : A) (a1 : A) :\n    Cubical.PathP (fn (i : Cubical.I) => Pair A A) (Pair.pair a1 a0) (Pair.pair a0 a1) :=\n    fn (i : Cubical.I) => Pair.pair a0 a1\n"

// --- Indexed families: constructor index inversion (Stage 3b) -------------
//
// `ctor_refine.mo` solves a constructor's declared indices against the
// scrutinee: `cons` against `Vec (succ n) A` binds `tail : Vec n A`, and `nil`
// there can never match, so it is not a missing arm. Each acceptance has a
// rejection twin: the same match with the index made abstract, or the body
// returning a value at the wrong length.

#[test]
def test_vhead_needs_no_nil_arm : IO Bool :=
    accepted
        ("def vh {n : Nat} {A : Type} (v : Vec (Nat.succ n) A) : A :=\n"
            ++ "    match v {\n"
            ++ "        Vec.cons a _ => a,\n"
            ++ "    }\n")

#[test]
def test_a_cons_only_match_on_an_abstract_length_is_not_exhaustive : IO Bool :=
    rejected_with "only_cons" "non-exhaustive match"
        ("def only_cons {n : Nat} {A : Type} (v : Vec n A) : Bool :=\n"
            ++ "    match v {\n"
            ++ "        Vec.cons _ _ => true,\n"
            ++ "    }\n")

#[test]
def test_vtail_types_the_tail_at_the_predecessor_length : IO Bool :=
    accepted
        ("def vt {n : Nat} {A : Type} (v : Vec (Nat.succ n) A) : Vec n A :=\n"
            ++ "    match v {\n"
            ++ "        Vec.cons _ t => t,\n"
            ++ "    }\n")

#[test]
def test_the_tail_is_not_the_whole_length : IO Bool :=
    rejected_with "vt_long" mismatch
        ("def vt_long {n : Nat} {A : Type} (v : Vec (Nat.succ n) A) : Vec (Nat.succ n) A :=\n"
            ++ "    match v {\n"
            ++ "        Vec.cons _ t => t,\n"
            ++ "    }\n")

#[test]
def test_a_concrete_length_prunes_the_other_constructor : IO Bool :=
    accepted
        ("def two_head (v : Vec (Nat.succ (Nat.succ Nat.zero)) I64) : I64 :=\n"
            ++ "    match v {\n"
            ++ "        Vec.cons h _ => h,\n"
            ++ "    }\n")

#[test]
def test_vappend_refines_the_length_in_each_arm : IO Bool :=
    accepted
        ("def va {m : Nat} {n : Nat} {A : Type} (v : Vec m A) (w : Vec n A) : Vec (Nat.add m n) A :=\n"
            ++ "    match v {\n"
            ++ "        Vec.nil => w,\n"
            ++ "        Vec.cons h t => Vec.cons h (va t w),\n"
            ++ "    }\n")

#[test]
def test_an_unrefinable_arm_is_still_rejected : IO Bool :=
    rejected_with "va_wrong" mismatch
        ("def va_wrong {m : Nat} {n : Nat} {A : Type} (v : Vec m A) (w : Vec n A) : Vec (Nat.add n m) A :=\n"
            ++ "    match v {\n"
            ++ "        Vec.nil => w,\n"
            ++ "        Vec.cons h t => Vec.cons h (va_wrong t w),\n"
            ++ "    }\n")

// --- Indexed families: constructor introduction (Stage 3c) ------------------
//
// A constructor application checked against an indexed expected type must
// produce its indices. Only a constructor-head clash is rejected; a variable
// length on either side may be refined by a match the checker does not track.

#[test]
def test_nil_is_not_a_vector_of_length_one : IO Bool :=
    rejected_with "nil_one" mismatch "def nil_one : Vec 1 I64 := Vec.nil\n"

#[test]
def test_a_unary_length_is_checked_like_a_literal : IO Bool :=
    rejected_with "nil_succ" mismatch "def nil_succ : Vec (Nat.succ Nat.zero) I64 := Vec.nil\n"

#[test]
def test_a_nested_constructor_is_checked_at_its_own_length : IO Bool :=
    rejected_with "one_for_two" mismatch "def one_for_two : Vec 2 I64 := Vec.cons 1 Vec.nil\n"

#[test]
def test_cons_is_not_a_vector_of_length_zero : IO Bool :=
    rejected_with "cons_zero" mismatch "def cons_zero : Vec Nat.zero I64 := Vec.cons 1 Vec.nil\n"

#[test]
def test_a_typed_tail_supplies_its_length : IO Bool :=
    rejected_with "tail_len" mismatch "def tail_len (t : Vec 0 I64) : Vec 0 I64 := Vec.cons 1 t\n"

#[test]
def test_constructors_at_their_own_length_are_accepted : IO Bool :=
    accepted
        ("def v0 : Vec 0 I64 := Vec.nil\n"
            ++ "def v1 : Vec 1 I64 := Vec.cons 1 Vec.nil\n"
            ++ "def v2 : Vec (Nat.succ (Nat.succ Nat.zero)) I64 := Vec.cons 1 (Vec.cons 2 Vec.nil)\n"
            ++ "def vs {n : Nat} (t : Vec n I64) : Vec (Nat.succ n) I64 := Vec.cons 1 t\n")

#[test]
def test_a_constructor_scrutinee_prunes_by_its_own_length : IO Bool :=
    accepted
        ("def m0 : Bool := match Vec.nil { Vec.nil => true }\n"
            ++ "def m1 : Bool := match Vec.cons 42 Vec.nil { Vec.cons h t => match t { Vec.nil => true } }\n")
