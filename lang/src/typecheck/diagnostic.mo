/// Human-readable rendering for `TypeError` (`lang/types.mo`) — the
/// type-checking counterpart to `lang/parser/diagnostic.mo`'s
/// `render_parse_error`, mirroring how the Rust reference splits parse
/// vs. type diagnostics across `core/src/parser/error.rs` and
/// `core/src/eval/type.rs::type_error_as_diagnostics`.
///
/// Unlike `ParseError`, `TypeError` (and `Term` generally) carries no
/// source location at all — there is no span/offset anywhere in the AST
/// once parsing is done. So a rendered `TypeError` can say *which
/// declaration* failed and *why*, but not *line:column* the way a parse
/// error can — `render_type_error` takes a `context_name` (typically a
/// declaration's name) to stand in for that missing location. Threading
/// real spans through `Term` construction across the whole grammar
/// would be a much larger project and isn't attempted here.

use lib::types {NameRef, TypeError, show_identifier, show_name_path, show_operator, show_qualified_name}
use lib::pretty {show_term}

/// `NameRef` (`lang/types.mo`) has no `Show`/to-string helper of its
/// own yet — the variants wrap `Identifier`/`NamePath`/`QualifiedName`/
/// `Operator`, each of which already has one.
#[partial]
def name_ref_to_string (n : NameRef) : String :=
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
def type_error_message (e : TypeError) : String :=
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
	}

/// Render a full diagnostic for a type error — same visual family as
/// `render_parse_error`'s header/arrow-line
/// (`lang/parser/diagnostic.mo`), just without a line:col (see this
/// file's header comment).
#[partial]
def render_type_error (context_name : String) (path : Option String) (e : TypeError) : String :=
	let msg : String := type_error_message e in
	let header : String := String.concat "error: " (String.concat msg (String.concat " in " (String.concat context_name "\n"))) in
	let path_str : String := match path {
		Option.some p => p,
		Option.none => "",
	} in
	String.concat header (String.concat "  --> " (String.concat path_str "\n"))

// --- Tests ---

#[test]
def test_type_error_message_mismatch : Bool :=
	String.beq (type_error_message (TypeError.mismatch (Term.type_ 1) (Term.type_ 2))) "type mismatch: expected Type, found Type 1"

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
