/// Human-readable rendering for `TypeError` (`lang/types.mo`) — the
/// type-checking counterpart to `lang/parser/diagnostic.mo`'s
/// `render_parse_error`, mirroring how the Rust reference splits parse
/// vs. type diagnostics across `core/src/parser/error.rs` and
/// `core/src/eval/type.rs::type_error_as_diagnostics`.
///
/// Unlike `ParseError`, `TypeError` carries no source location — but that
/// is a fact about the ERROR, not about the AST. Terms DO carry locations
/// (`Term.ctx` wrappers, built by the located parse that every path runs:
/// see `Term.ctx`'s own doc in `lang/src/types.mo`); none of them reaches a
/// payload. `type_check_located` discards the location when the check
/// FAILS (`lang/src/typecheck/infer.mo`'s `err e => err e`), `unify` peels
/// wrappers at entry (`lang/src/typecheck/unify.mo`), and the
/// name-resolution variants — `unknown_var`, the most common diagnostic
/// there is — have no term field to carry one at all. So a rendered
/// `TypeError` can say *which declaration* failed and *why*, but not
/// *line:column* the way a parse error can — `render_type_error` takes a
/// `context_name` (typically a declaration's name) to stand in for that
/// missing location. This is measured, not assumed: the five probes in
/// `lang/src/tests/unify_tests.mo` pin it, including the nested-operand
/// case, where a payload can have a bare root and a LOCATED child.
/// Attaching the location at the innermost enclosing located node is the
/// follow-up that would make ranges expression-granular; it is not
/// attempted here.

use lang::types {
  Identifier, NameRef, TypeError, concrete, id, show_identifier, show_name_path,
  show_operator, show_qualified_name, sort,
}
use lib::pretty {show_term}

/// `NameRef` (`lang/types.mo`) has no `Show`/to-string helper of its
/// own yet — the variants wrap `Identifier`/`NamePath`/`QualifiedName`/
/// `Operator`, each of which already has one.
#[partial]
pub def name_ref_to_string (n : NameRef) : String :=
	match n {
		// A `nid` may hold a FLATTENED qualified reference: the parse
		// lowering renders a `nqn` in the def-side symbol convention
		// (`std.process::process_id`) so references and definitions agree
		// for codegen, and the checker rebuilds it as a bare `nid`.
		// Printing that verbatim shows an internal spelling the user
		// never wrote -- restore the SOURCE form for display.
		NameRef.nid id => show_source_spelling id,
		NameRef.nnp np => show_name_path np,
		NameRef.nqn qn => show_qualified_name qn,
		NameRef.nop op => show_operator op,
	}

/// A human-readable description of what went wrong — one line per
/// `TypeError` variant (`lang/types.mo:252`).
#[partial]
pub def type_error_message (e : TypeError) : String :=
	match e {
		TypeError.mismatch expected actual =>
			String.concat "type mismatch: expected " (String.concat (show_term expected) (String.concat ", found " (show_term actual))),
		TypeError.unknown_var name =>
			String.concat "unknown variable '" (String.concat (name_ref_to_string name) "'"),
		TypeError.unknown_type name =>
			String.concat "unknown type '" (String.concat (name_ref_to_string name) "'"),
		TypeError.unknown_constructor name =>
			String.concat "unknown constructor '" (String.concat (name_ref_to_string name) "'"),
		TypeError.not_a_function term =>
			String.concat "not a function: " (show_term term),
		TypeError.not_a_type term =>
			String.concat "not a type: " (show_term term),
		TypeError.infinite_type term =>
			String.concat "infinite type: " (show_term term),
		TypeError.custom msg => msg,
		// The affine-by-default experiment's three
		// (Milestone 2).
		// Each names the remedy that actually applies rather than just
		// reporting a count, because under Design B the three cases
		// have genuinely different fixes.
		TypeError.copy_required name typ uses =>
			String.concat "`" (String.concat (show_identifier name)
				(String.concat "` : " (String.concat (show_term typ)
				(String.concat " is used " (String.concat (I64.to_string uses)
				" times but is affine; borrow it, or give its type a Copy instance"))))),
		TypeError.value_used_after_move name typ owning =>
			String.concat "`" (String.concat (show_identifier name)
				(String.concat "` : " (String.concat (show_term typ)
				(String.concat " is moved " (String.concat (I64.to_string owning)
				" times; no borrow can fix this -- it needs Copy, Clone, or a rewrite"))))),
		TypeError.linear_unused name typ =>
			String.concat "linear `" (String.concat (show_identifier name)
				(String.concat "` : " (String.concat (show_term typ)
				" is never used; linear means exactly once"))),
	}

/// Render a full diagnostic for a type error — same visual family as
/// `render_parse_error`'s header/arrow-line
/// (`lang/parser/diagnostic.mo`), just without a line:col (see this
/// file's header comment).
#[partial]
pub def render_type_error (context_name : String) (path : Option String) (e : TypeError) : String :=
	render_type_diagnostic "error: " context_name path e

/// The shared body. `severity` is the whole prefix, trailing space included.
///
/// Split out, with the severity word coming from the CALLER, for the warning
/// renderer the self-hosted checker does not have yet: `type_error_message` is
/// prefix-free, so a demoted diagnostic can never read `warning: error: ...`.
/// Adding that sibling is part of the severity-aware `check` loop
/// `lang/module.mo`'s `Diagnostic` note describes -- not something to land
/// alone, because nothing can route a warning to a printer today.
#[partial]
def render_type_diagnostic (severity : String) (context_name : String) (path : Option String) (e : TypeError) : String :=
	let msg : String := type_error_message e in
	let header : String := String.concat severity (String.concat msg (String.concat " in " (String.concat context_name "\n"))) in
	let path_str : String := match path {
		Option.some p => p,
		Option.none => "",
	} in
	String.concat header (String.concat "  --> " (String.concat path_str "\n"))

// --- Tests ---

#[test]
def test_type_error_message_mismatch : Bool :=
	String.beq (type_error_message (TypeError.mismatch (Term.sort (SortLevel.concrete 1)) (Term.sort (SortLevel.concrete 2)))) "type mismatch: expected Type, found Type 1"

#[test]
def test_type_error_message_unknown_var : Bool :=
	String.beq (type_error_message (TypeError.unknown_var (NameRef.nid (Identifier.id "foo")))) "unknown variable 'foo'"

#[test]
def test_type_error_message_unknown_type : Bool :=
	String.beq (type_error_message (TypeError.unknown_type (NameRef.nid (Identifier.id "Bar")))) "unknown type 'Bar'"

#[test]
def test_type_error_message_unknown_constructor : Bool :=
	String.beq (type_error_message (TypeError.unknown_constructor (NameRef.nid (Identifier.id "Baz")))) "unknown constructor 'Baz'"

#[test]
def test_type_error_message_custom : Bool :=
	String.beq (type_error_message (TypeError.custom "something went wrong")) "something went wrong"

#[test]
def test_render_type_error_includes_context_and_path : Bool :=
	let rendered : String := render_type_error "my_def" (Option.some "examples/foo.mo") (TypeError.custom "bad thing") in
	String.contains rendered "error: bad thing in my_def"
		&& String.contains rendered "--> examples/foo.mo"

#[test]
def test_render_type_error_no_path : Bool :=
	let rendered : String := render_type_error "my_def" Option.none (TypeError.custom "bad thing") in
	String.contains rendered "error: bad thing in my_def"
		&& String.contains rendered "-->"


/// An identifier as the user would have written it. Only a flattened
/// qualified reference differs: its module half is dot-joined internally
/// and `::`-joined in source. Everything else passes through untouched.
#[partial]
def show_source_spelling (id : Identifier) : String :=
	let text : String := show_identifier id in
	let cut : I64 := source_spelling_sep text 0 in
	if cut < 0 then text
	else String.concat (dots_to_colons (String.slice text 0 cut)) (String.drop cut text)

/// Index of the `::` separating the module half from the name half, or
/// -1 when there is none. Only the FIRST `::` matters: a minted name has
/// exactly one, and the name half's own `.`s must be left alone.
#[partial]
def source_spelling_sep (s : String) (i : I64) : I64 :=
	if i + 1 < String.length s then
		if String.beq (String.slice s i 2) "::" then i
		else source_spelling_sep s (i + 1)
	else (0 - 1)

/// Rewrite `.` to `::` in a module half. Byte-wise rebuild rather than
/// split+intercalate: the list-accumulator form tripped the self-hosted
/// checker (`expected (List String), found (List A)`), and this needs no
/// list at all.
#[partial]
def dots_to_colons (s : String) : String := dots_to_colons_go s 0 ""

#[partial]
def dots_to_colons_go (s : String) (i : I64) (acc : String) : String :=
	if i < String.length s then
		match String.get s i {
			Option.some b =>
				if U8.beq b 46u8
				then dots_to_colons_go s (i + 1) (String.concat acc "::")
				else dots_to_colons_go s (i + 1) (String.concat acc (String.slice s i 1)),
			Option.none => acc,
		}
	else acc

/// A flattened qualified reference prints as the user WROTE it: module
/// half `::`-joined, not the dot-joined internal symbol spelling.
#[test]
def test_flattened_qualified_prints_source_spelling : Bool :=
	String.beq
		(name_ref_to_string (NameRef.nid (Identifier.id "std.process::process_id")))
		"std::process::process_id"

/// The NAME half keeps its dots -- `IO.println` is a dotted def name,
/// not a module path, and must not become `IO::println`.
#[test]
def test_flattened_qualified_keeps_dotted_name_half : Bool :=
	String.beq
		(name_ref_to_string (NameRef.nid (Identifier.id "std.io::IO.println")))
		"std::io::IO.println"

/// An ordinary dotted name has no `::` and passes through untouched.
#[test]
def test_plain_dotted_name_is_unchanged : Bool :=
	String.beq
		(name_ref_to_string (NameRef.nid (Identifier.id "List.cons")))
		"List.cons"

#[test]
def test_type_error_message_copy_required : Bool :=
	// The message must name the remedy, not just the count -- the
	// whole point of splitting this from `value_used_after_move`.
	let e : TypeError := TypeError.copy_required (Identifier.id "s") (Term.sort (SortLevel.concrete 1)) 3 in
	String.contains (type_error_message e) "borrow it, or give its type a Copy instance"

#[test]
def test_type_error_message_value_used_after_move : Bool :=
	let e : TypeError := TypeError.value_used_after_move (Identifier.id "t") (Term.sort (SortLevel.concrete 1)) 2 in
	String.contains (type_error_message e) "no borrow can fix this"

#[test]
def test_type_error_message_linear_unused : Bool :=
	let e : TypeError := TypeError.linear_unused (Identifier.id "h") (Term.sort (SortLevel.concrete 1)) in
	String.contains (type_error_message e) "never used"
