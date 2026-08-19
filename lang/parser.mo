/// Self-hosted Monad grammar parser.
/// Split into modules for maintainability.
use lang.types {
  ClassDef, DebugName, Decl, Def, DoStmt, Identifier, InductConstructor,
  LocatedSpan, Location, MatchCase, ModulePath, NameRef, OpenFilter, Operator,
  Param, StructField, Term, TermV0, TypeConstraint, UseFilter, UseItem, app,
  bind_s, class_d, con, ctx, custom, def_d, desugar_do, expr_s, forall, hole,
  id, if_, inductive_d, infix_d, instance_d, lam, let_s, list_reverse, lit,
  match_, mc, mk, mp, name, named, nid, nmp, nop, ntv, open_all, open_d,
  open_only, operator, param_many, pi, ret_s, scoped_open_d, show_identifier,
  show_operator, struct_d, type_, unnamed, use_bare, use_d, use_glob, use_items,
  use_name, use_rename, use_sub, use_sub_rename, var,
}
use std.list {filter, length}
use lang.parser.core {
  ParseResult, custom, fail, is_empty, mk, op_char_member, op_chars,
  op_lookup_prec, op_table, parse_error_remaining, success, tag,
}
use lang.parser.char_preds {is_ident_char, is_space}
use lang.parser.combinators {
  alt, alt_fold, bind_parse, delimited_by, many1, map_parse, opt,
  preceded_by, separated_by, tag, take_while, terminated_by,
}
use lang.parser.number {number, numeric_literal}
use lang.parser.whitespace {skip_spaces, skip_spaces_match, ws0, ws1}
use lang.parser.position {consume_span, location_of_remaining, new_span, span_fragment, span_location}
use lang.parser.identifier {identifier}
use lang.parser.string {string_parse}
use lang.parser.diagnostic {render_parse_error}
open lang.parser.core {
  ParseResult, custom, fail, is_empty, mk, op_char_member, op_chars,
  op_lookup_prec, op_table, success, tag,
}
open ParseResult {fail, success}

#[partial]
def at_least_two (ids : List String) : Bool :=
	Bool.not (List.is_empty (List.tail ids))

def dotted_identifier (input : String) : ParseResult (List String) :=
	separated_by (tag ".") identifier input

/// Join a list of identifiers into a dotted string (e.g., ["Unit", "unit"] -> "Unit.unit")
#[partial]
def join_dotted_identifiers (ids : List String) : String := match ids {
    List.empty => "",
    List.cons hd rest => join_dotted_rest hd rest,
}

#[partial]
def join_dotted_rest (hd : String) (rest : List String) : String := match rest {
    List.empty => hd,
    List.cons x y => String.concat (String.concat hd ".") (join_dotted_identifiers rest),
}

/// Extract the identifier string from a NameRef
#[partial]
def name_ref_to_string (nref : NameRef) : Option String := match nref {
    NameRef.nid id => Option.some (show_identifier id),
    NameRef.nmp mp => Option.some (module_path_to_string mp),
    NameRef.nop op => Option.some (show_operator op),
}

/// Convert a ModulePath to a dotted string
#[partial]
def module_path_to_string (mp : ModulePath) : String := match mp {
    ModulePath.mp ids => join_dotted_identifiers (map_show_identifier ids),
}

/// Map a list of Identifiers to their string representations
#[partial]
def map_show_identifier (ids : List Identifier) : List String := match ids {
    List.empty => List.empty,
    List.cons hd rest => List.cons (show_identifier hd) (map_show_identifier rest),
}

/// Show an Identifier as a string
#[partial]
def show_identifier (id : Identifier) : String := match id {
    Identifier.id s => s,
}

/// Show an Operator as a string
#[partial]
def show_operator (op : Operator) : String := match op {
    Operator.operator s => s,
}

/// Find the last occurrence of a substring in a string, return its index or -1
#[partial]
def string_find_last (haystack : String) (needle : String) : I64 :=
    if String.beq needle "" then -1
    else if I64.gt (String.length needle) (String.length haystack) then -1
    else string_find_last_loop haystack needle (String.length haystack - String.length needle)

#[partial]
def string_find_last_loop (haystack : String) (needle : String) (start_idx : I64) : I64 :=
    if I64.lt start_idx 0 then -1
    else if String.beq (String.slice haystack start_idx (start_idx + String.length needle)) needle then start_idx
    else string_find_last_loop haystack needle (start_idx - 1)

#[partial]
def path_variable (input : String) : ParseResult TermV0 :=
        match dotted_identifier input {
                success rem ids =>
                        if at_least_two ids
                        then success rem (TermV0.var (NameRef.nmp (ModulePath.mp (List.map Identifier.id ids))))
                        else fail (ParseError.custom "not a dotted path" rem),
                fail e => fail e
        }

#[partial]
def do_stmts_tail (input : String) : String :=
	do_stmts_tail_sp (take_while is_space input) input

#[partial]
def do_stmts_tail_sp (r : ParseResult String) (orig : String) : String :=
	match r {
		success rem _ => do_stmts_tail_semi (tag ";" rem) rem orig,
		fail _ => orig
	}

#[partial]
def do_stmts_tail_semi (r : ParseResult String) (after_sp : String) (orig : String) : String :=
	match r {
		success rem _ => skip_docstrings (skip_spaces rem),
		fail _ => after_sp
	}

#[partial]
def do_stmt_return (ctx: List Identifier) (input: String) : ParseResult DoStmt :=
    do_stmt_ret_kw (tag "return" input) input ctx

#[partial]
def do_stmt_ret_kw (r: ParseResult String) (orig: String) (ctx: List Identifier) : ParseResult DoStmt :=
    match r {
        success rem _ => do_stmt_ret_expr (expression ctx (skip_docstrings (skip_spaces rem))),
        fail _ => do_stmt_try_let (tag "let" (skip_spaces orig)) orig ctx
    }

#[partial]
def do_stmt_ret_expr (r: ParseResult Term) : ParseResult DoStmt :=
    match r {
        success rem value => success rem (DoStmt.ret_s value),
        fail e => fail e
    }

#[partial]
def do_stmt_try_let (r: ParseResult String) (orig: String) (ctx: List Identifier) : ParseResult DoStmt :=
    match r {
        success rem _ => do_stmt_let_name (identifier (skip_spaces rem)) ctx,
        fail _ => do_stmt_expr (expression ctx (skip_docstrings (skip_spaces orig)))
    }

#[partial]
def do_stmt_let_name (r: ParseResult String) (ctx: List Identifier) : ParseResult DoStmt :=
    match r {
        success rem name => do_stmt_let_kind rem (Identifier.id name) ctx,
        fail e => fail e
    }

#[partial]
def do_stmt_let_kind (input: String) (name: Identifier) (ctx: List Identifier) : ParseResult DoStmt :=
    do_stmt_let_kind_try (tag ":=" (skip_spaces input)) name input ctx

#[partial]
def do_stmt_let_kind_try (r: ParseResult String) (name: Identifier) (orig: String) (ctx: List Identifier) : ParseResult DoStmt :=
    match r {
        success rem _ => do_stmt_let_value (expression ctx (skip_docstrings (skip_spaces rem))) name Term.hole,
        fail _ => do_stmt_bind_arrow (tag "<-" (skip_spaces orig)) name orig ctx
    }

#[partial]
def do_stmt_let_value (r: ParseResult Term) (name: Identifier) (typ: Term) : ParseResult DoStmt :=
    match r {
        success rem value => success rem (DoStmt.let_s name typ value),
        fail e => fail e
    }

#[partial]
def do_stmt_bind_arrow (r: ParseResult String) (name: Identifier) (orig: String) (ctx: List Identifier) : ParseResult DoStmt :=
    match r {
        success rem _ => do_stmt_bind_value (expression ctx (skip_docstrings (skip_spaces rem))) name Term.hole,
        fail _ => do_stmt_let_try_type (tag ":" (skip_spaces orig)) name orig ctx
    }

// A do-block `let`/bind statement may carry an optional type annotation
// between the name and `:=`/`<-` (e.g. `let res : Result String X <-
// load_file_modules file_path;`) -- parsed here and threaded through into
// `DoStmt.let_s`/`bind_s` (lang/types.mo), which now carry the statement's
// own type (`Term.hole` when unannotated -- the two call sites above --
// or the real parsed type here). `desugar_do_inner` uses it directly.
#[partial]
def do_stmt_let_try_type (r: ParseResult String) (name: Identifier) (orig: String) (ctx: List Identifier) : ParseResult DoStmt :=
    match r {
        success rem _ => do_stmt_let_typed (type_expression ctx rem) name orig ctx,
        fail _ => fail (ParseError.custom "expected := or <- after let in do block" orig)
    }

#[partial]
def do_stmt_let_typed (r: ParseResult Term) (name: Identifier) (orig: String) (ctx: List Identifier) : ParseResult DoStmt :=
    match r {
        success rem typ => do_stmt_let_typed_kind (tag ":=" (skip_spaces rem)) name typ rem ctx,
        fail e => fail e
    }

#[partial]
def do_stmt_let_typed_kind (r: ParseResult String) (name: Identifier) (typ: Term) (orig: String) (ctx: List Identifier) : ParseResult DoStmt :=
    match r {
        success rem _ => do_stmt_let_value (expression ctx (skip_docstrings (skip_spaces rem))) name typ,
        fail _ => do_stmt_let_typed_bind (tag "<-" (skip_spaces orig)) name typ orig ctx
    }

#[partial]
def do_stmt_let_typed_bind (r: ParseResult String) (name: Identifier) (typ: Term) (orig: String) (ctx: List Identifier) : ParseResult DoStmt :=
    match r {
        success rem _ => do_stmt_bind_value (expression ctx (skip_docstrings (skip_spaces rem))) name typ,
        fail _ => fail (ParseError.custom "expected := or <- after let in do block" orig)
    }

#[partial]
def do_stmt_bind_value (r: ParseResult Term) (name: Identifier) (typ: Term) : ParseResult DoStmt :=
    match r {
        success rem value => success rem (DoStmt.bind_s name typ value),
        fail e => fail e
    }

#[partial]
def do_stmt_expr (r: ParseResult Term) : ParseResult DoStmt :=
    match r {
        success rem value => success rem (DoStmt.expr_s value),
        fail e => fail e
    }

#[partial]
def do_stmts_extend_ctx (stmt: DoStmt) (ctx: List Identifier) : List Identifier :=
    match stmt {
        bind_s name _ _ => List.cons name ctx,
        let_s name _ _ => List.cons name ctx,
        _ => ctx
    }

// `skip_docstrings (skip_spaces ...)` (not bare `skip_spaces`) throughout
// this statement sequencer -- a `//`/`///` comment between two do-block
// statements, or right before the closing `}`, must be skipped like
// whitespace here, same as `match_cases_parse`'s own comment-between-arms
// fix elsewhere in this file (`skip_spaces` alone leaves the `//` in
// place, which then fails to parse as the next statement/`}`).
#[partial]
def do_stmts (ctx: List Identifier) (input: String) : ParseResult (List DoStmt) :=
    do_stmts_check_end (tag "}" (skip_docstrings (skip_spaces input))) input ctx

#[partial]
def do_stmts_check_end (r: ParseResult String) (orig: String) (ctx: List Identifier) : ParseResult (List DoStmt) :=
    match r {
        success rem _ =>
            let empty : List DoStmt := List.empty in
            success rem empty,
        fail _ => do_stmts_first (do_stmt_return ctx (skip_docstrings (skip_spaces orig))) (skip_docstrings (skip_spaces orig)) ctx
    }

#[partial]
def do_stmts_first (r: ParseResult DoStmt) (orig: String) (ctx: List Identifier) : ParseResult (List DoStmt) :=
    match r {
        success rem stmt => do_stmts_next2 (do_stmts (do_stmts_extend_ctx stmt ctx) (do_stmts_tail rem)) stmt,
        fail e => fail e
    }

#[partial]
def do_stmts_next2 (r: ParseResult (List DoStmt)) (first: DoStmt) : ParseResult (List DoStmt) :=
    match r {
        success rem rest => success rem (List.cons first rest),
        fail e => fail e
    }

#[partial]
def do_parser (ctx: List Identifier) (input: String) : ParseResult Term :=
    do_parser_kw (tag "do" input) ctx

#[partial]
def do_parser_kw (r: ParseResult String) (ctx: List Identifier) : ParseResult Term :=
    match r {
        success rem _ => do_parser_open (tag "{" (skip_spaces rem)) ctx,
        fail e => fail e
    }

#[partial]
def do_parser_open (r: ParseResult String) (ctx: List Identifier) : ParseResult Term :=
    match r {
        success rem _ => do_parser_stmts (do_stmts ctx rem) ctx,
        fail e => fail e
    }

#[partial]
def do_parser_stmts (r: ParseResult (List DoStmt)) (ctx: List Identifier) : ParseResult Term :=
    match r {
        success rem stmts => do_parser_desugar rem stmts,
        fail e => fail e
    }

#[partial]
def do_parser_desugar (rem: String) (stmts: List DoStmt) : ParseResult Term :=
    success rem (desugar_do stmts)

#[partial]
def is_newline (c : String) : Bool :=
	String.beq c "\n"

#[partial]
def is_not_newline (c : String) : Bool :=
	if String.beq c "\n" then false
	else true

#[partial]
def is_close_curly (c : String) : Bool :=
	String.beq c "}"

#[partial]
def is_not_close_curly (c : String) : Bool :=
	if String.beq c "}" then false
	else true

#[partial]
def is_not_close_paren (c : String) : Bool :=
	if String.beq c ")" then false
	else true

#[partial]
def is_op_char (c : String) : Bool :=
	op_char_member c op_chars

#[partial]
def op_check (s : String) (rem : String) : ParseResult String :=
	if is_empty s
	then fail (ParseError.custom "expected operator" rem)
	else if I64.beq 0 (op_precedence s)
		then fail (ParseError.custom "unknown operator" rem)
		else success rem s

#[partial]
def operator_parse (input : String) : ParseResult String :=
	bind_parse (take_while is_op_char) op_check input

#[partial]
def op_precedence (op : String) : I64 :=
	op_lookup_prec op op_table

#[partial]
def ids_to_module_path (ids : List String) : ModulePath :=
	ModulePath.mp (List.map Identifier.id ids)

#[partial]
def module_path_parser (input : String) : ParseResult ModulePath :=
	map_parse ids_to_module_path dotted_identifier input

// use module.path

#[partial]
def is_not_bracket (c : String) : Bool :=
	if String.beq "]" c then false
	else true

#[partial]
def is_not_attr_end (c : String) : Bool :=
	if String.beq "]" c then false
	else true

/// Skip one leading `#[...]` attribute clause (e.g. `#[terminating]`),
/// if present — a no-op (returns `input` unchanged) otherwise. Reused
/// by `instance_methods` for per-method attributes (real usage:
/// `std/map.mo`'s `#[terminating] def insert ...` inside `instance [BOrd
/// K] Map BTreeMap { ... }`) — top-level `def`s already handle this via
/// `def_try_attrs`/`def_attr_skip`, but instance methods went through
/// `instance_methods`'s own separate, attribute-unaware `tag "def"`
/// check, so any attributed method broke the ENTIRE enclosing
/// `instance` block (a failed method fails the whole `instance_methods`
/// loop, which fails the whole `instance` decl, which — via
/// `decls_try`'s truncate-on-fail — silently dropped everything after
/// it in the file).
#[partial]
def skip_one_attr (input : String) : String :=
	skip_one_attr_try (tag "#[" input) input

#[partial]
def skip_one_attr_try (r : ParseResult String) (orig : String) : String :=
	match r {
		success rem _ => skip_one_attr_content (take_while is_not_attr_end rem) orig,
		fail _ => orig
	}

#[partial]
def skip_one_attr_content (r : ParseResult String) (orig : String) : String :=
	match r {
		success rem _ =>
			match tag "]" rem {
				success rem2 _ => skip_spaces rem2,
				fail _ => orig
			},
		fail _ => orig
	}

// ─── Real attribute (`#[name arg1 arg2 ...]`) parsing ──────────────────
//
// Mirrors the Rust reference's `attribute_parser`/`attr_arg_parser`/
// `opt_attributes` (core/src/parser.rs) — builds real `Attribute`/
// `AttrArg` data instead of `skip_one_attr`/`def_try_attrs`'s own
// skip-and-discard. IS wired into `def_parser`/`type_parser`/`Def`/
// `Inductive` construction (`opt_attributes` is called from
// `def_parser`, `type_parser`, and `def_explicit_attrs` below) — this
// comment used to say "NOT YET WIRED", staged as its own standalone
// piece; that staging is done, the comment just never got updated.

/// One `#[...]` attribute argument. Only bare `ident`/`str`/`num` args
/// are exercised by any real corpus attribute (confirmed: no `.mo` file
/// anywhere uses `name := value` or bracketed `[...]` group syntax) —
/// the `named`/`group` alternatives below are included for structural
/// completeness against the reference grammar but are correspondingly
/// lower-confidence/less-tested.
#[partial]
def attr_arg_parser (input : String) : ParseResult AttrArg :=
	attr_arg_try_group (tag "[" input) input

#[partial]
def attr_arg_try_group (r : ParseResult String) (orig : String) : ParseResult AttrArg :=
	match r {
		success rem _ => attr_arg_group_items (skip_spaces rem) List.empty,
		fail _ => attr_arg_try_named_block (tag "{" orig) orig
	}

#[partial]
def attr_arg_group_items (input : String) (acc : List AttrArg) : ParseResult AttrArg :=
	match attr_arg_parser input {
		success rem item => attr_arg_group_sep (skip_spaces rem) (List.cons item acc),
		fail _ => attr_arg_group_close input (list_reverse acc)
	}

#[partial]
def attr_arg_group_sep (input : String) (acc : List AttrArg) : ParseResult AttrArg :=
	match tag "," input {
		success rem _ => attr_arg_group_items (skip_spaces rem) acc,
		fail _ => attr_arg_group_close input (list_reverse acc)
	}

#[partial]
def attr_arg_group_close (input : String) (items : List AttrArg) : ParseResult AttrArg :=
	match tag "]" (skip_spaces input) {
		success rem _ => success rem (AttrArg.group items),
		fail e => fail (ParseError.custom "expected ] to close attribute arg group" input)
	}

#[partial]
def attr_arg_try_named_block (r : ParseResult String) (orig : String) : ParseResult AttrArg :=
	match r {
		success rem _ => attr_arg_named_items (skip_spaces rem) List.empty,
		fail _ => attr_arg_try_bare orig
	}

#[partial]
def attr_arg_named_items (input : String) (acc : List AttrArg) : ParseResult AttrArg :=
	match attr_arg_named_one input {
		success rem item => attr_arg_named_sep (skip_spaces rem) (List.cons item acc),
		fail _ => attr_arg_named_close input (list_reverse acc)
	}

#[partial]
def attr_arg_named_one (input : String) : ParseResult AttrArg :=
	match identifier input {
		success rem name => attr_arg_named_val (tag ":=" (skip_spaces rem)) (Identifier.id name),
		fail e => fail e
	}

#[partial]
def attr_arg_named_val (r : ParseResult String) (name : Identifier) : ParseResult AttrArg :=
	match r {
		success rem _ => attr_arg_named_value (attr_arg_parser (skip_spaces rem)) name,
		fail e => fail e
	}

#[partial]
def attr_arg_named_value (r : ParseResult AttrArg) (name : Identifier) : ParseResult AttrArg :=
	match r {
		success rem v => success rem (AttrArg.named name v),
		fail e => fail e
	}

#[partial]
def attr_arg_named_sep (input : String) (acc : List AttrArg) : ParseResult AttrArg :=
	match tag "," input {
		success rem _ => attr_arg_named_items (skip_spaces rem) acc,
		fail _ => attr_arg_named_close input (list_reverse acc)
	}

/// A `{name := value, ...}` block wraps its entries in a single
/// `AttrArg.group` here, rather than flattening each `named` entry
/// directly onto the enclosing attribute's own arg list the way the
/// Rust reference's `attr_arg_parser` does (it returns a `Vec<AttrArg>`
/// per call specifically to support that flattening) — a deliberate
/// simplification: with zero real corpus usage of this form either
/// way, matching the reference's own multi-return-per-call shape isn't
/// worth the added complexity it would need throughout this whole
/// chain (`attr_arg_parser` would need to return `List AttrArg`
/// everywhere, not just here).
#[partial]
def attr_arg_named_close (input : String) (items : List AttrArg) : ParseResult AttrArg :=
	match tag "}" (skip_spaces input) {
		success rem _ => success rem (AttrArg.group items),
		fail e => fail (ParseError.custom "expected } to close attribute named block" input)
	}

#[partial]
def attr_arg_try_bare (input : String) : ParseResult AttrArg :=
	attr_arg_try_str (string_parse input) input

#[partial]
def attr_arg_try_str (r : ParseResult Term) (orig : String) : ParseResult AttrArg :=
	match r {
		success rem t => success rem (term_lit_to_attr_str t),
		fail _ => attr_arg_try_num (numeric_literal orig) orig
	}

/// `string_parse` only ever succeeds with a `Term.lit (Literal.str _)`
/// shape — this is a total function over that guaranteed shape, not a
/// general `Term -> AttrArg` conversion.
#[partial]
def term_lit_to_attr_str (t : Term) : AttrArg :=
	match t { Term.lit l => match l { Literal.str s => AttrArg.str s } }

#[partial]
def attr_arg_try_num (r : ParseResult Term) (orig : String) : ParseResult AttrArg :=
	match r {
		success rem t => success rem (term_lit_to_attr_num t),
		fail _ => attr_arg_try_ident (identifier orig)
	}

/// `numeric_literal` only ever succeeds with a `Term.lit (Literal.num _
/// _)` shape here — see `term_lit_to_attr_str`'s own doc comment.
#[partial]
def term_lit_to_attr_num (t : Term) : AttrArg :=
	match t { Term.lit l => match l { Literal.num n _ => AttrArg.num n } }

#[partial]
def attr_arg_try_ident (r : ParseResult String) : ParseResult AttrArg :=
	match r {
		success rem name => success rem (AttrArg.ident (Identifier.id name)),
		fail e => fail e
	}

/// One `#[name arg1 arg2 ...]` attribute. Mirrors `attribute_parser`
/// (core/src/parser.rs): `"#["`, the attribute's own name, then zero or
/// more whitespace-separated args, `"]"`.
#[partial]
def attribute_parser (input : String) : ParseResult Attribute :=
	attribute_open (tag "#[" input)

#[partial]
def attribute_open (r : ParseResult String) : ParseResult Attribute :=
	match r {
		success rem _ => attribute_name (identifier (skip_spaces rem)),
		fail e => fail e
	}

#[partial]
def attribute_name (r : ParseResult String) : ParseResult Attribute :=
	match r {
		success rem name => attribute_args (skip_spaces rem) (Identifier.id name) List.empty,
		fail e => fail e
	}

#[partial]
def attribute_args (input : String) (name : Identifier) (acc : List AttrArg) : ParseResult Attribute :=
	match attr_arg_parser input {
		success rem arg => attribute_args (skip_spaces rem) name (List.cons arg acc),
		fail _ => attribute_close input name (list_reverse acc)
	}

#[partial]
def attribute_close (input : String) (name : Identifier) (args : List AttrArg) : ParseResult Attribute :=
	match tag "]" (skip_spaces input) {
		success rem _ => success rem (Attribute.mk name args),
		fail e => fail (ParseError.custom "expected ] to close attribute" input)
	}

/// Zero or more stacked attributes ahead of a declaration (`#[a]\n#[b]\n
/// def ...`). Mirrors `opt_attributes` (core/src/parser.rs).
#[partial]
def opt_attributes (input : String) : ParseResult (List Attribute) :=
	opt_attributes_go (skip_spaces input) List.empty

#[partial]
def opt_attributes_go (input : String) (acc : List Attribute) : ParseResult (List Attribute) :=
	match attribute_parser input {
		success rem attr => opt_attributes_go (skip_spaces rem) (List.cons attr acc),
		fail _ => success input (list_reverse acc)
	}

#[partial]
def lam_params (params : List Param) (body : Term) : Term :=
	let rev : List Param := list_reverse params in
	lam_params_loop rev body

#[partial]
def lam_params_loop (params : List Param) (body : Term) : Term :=
	match params {
		List.cons p rest =>
			match p {
				Param.mk name type_ mult default _attrs =>
					lam_params_loop rest (Term.lam (DebugName.named name) type_ body)
			},
		List.empty => body
	}

#[partial]
def def_to_decl (body : Term) (name : Identifier) (typ : Term) (vis : Visibility) : Decl :=
	let empty_constraints : List TypeConstraint := List.empty in
	let empty_attrs : List Attribute := List.empty in
	Decl.def_d (Def.mk (ModulePath.mp (List.cons name List.empty)) typ body empty_constraints empty_attrs vis)

// --- Canonical declaration parsers (de Bruijn Term) ---

// Helper: build de Bruijn binding context from param names (reversed = innermost first).

#[partial]
def ctx_of_params (params : List Param) : List Identifier :=
	let empty_ctx : List Identifier := List.empty in
	ctx_of_params_loop params empty_ctx

#[partial]
def ctx_of_params_loop (params : List Param) (acc : List Identifier) : List Identifier :=
	match params {
		List.cons p rest =>
			match p {
				Param.mk name type_ mult default _attrs =>
					ctx_of_params_loop rest (List.cons name acc)
			},
		List.empty => acc
	}

// Shared `{ ... }` brace-list helpers for `use`/`open` filters. `brace_open`
// consumes `{` plus any following whitespace so the item parser starts
// clean; `brace_close` skips leading whitespace before matching `}`, since
// the item/separator parsers don't skip trailing whitespace themselves.

def brace_open (input : String) : ParseResult String :=
	match tag "{" input {
		success rem out => success (skip_spaces rem) out,
		fail e => fail e
	}

def brace_close (input : String) : ParseResult String :=
	tag "}" (skip_spaces input)

def brace_sep (input : String) : ParseResult String :=
	match tag "," (skip_spaces input) {
		success rem out => success (skip_spaces rem) out,
		fail e => fail e
	}

def as_kw (input : String) : ParseResult String :=
	tag "as" (skip_spaces input)

// use module.path { items }
//
// A single item inside `use Module { ... }`: `*` (glob), `name`,
// `name as alias`, `name { items }` (sub-module), or
// `name as alias { items }` (renamed sub-module). Tried in that order
// since each is a strict prefix of the next — alt_fold retries every
// alternative from the same original input on failure, so no manual
// backtracking is needed here.

#[partial]
def use_brace_item (input : String) : ParseResult UseItem :=
	alt_fold [use_brace_item_glob, use_brace_item_sub_rename, use_brace_item_sub,
	          use_brace_item_rename, use_brace_item_name] input

def use_brace_item_glob (input : String) : ParseResult UseItem :=
	match tag "*" input {
		success rem _ => success rem UseItem.use_glob,
		fail e => fail e
	}

def use_brace_item_name (input : String) : ParseResult UseItem :=
	match identifier input {
		success rem name => success rem (UseItem.use_name (Identifier.id name)),
		fail e => fail e
	}

#[partial]
def use_brace_item_rename (input : String) : ParseResult UseItem :=
	match identifier input {
		success rem name => use_brace_item_rename_alias name rem,
		fail e => fail e
	}

def use_brace_item_rename_alias (name : String) (input : String) : ParseResult UseItem :=
	match as_kw (skip_spaces input) {
		success rem _ => match identifier (skip_spaces rem) {
			success rem2 alias => success rem2 (UseItem.use_rename (Identifier.id name) (Identifier.id alias)),
			fail e => fail e
		},
		fail e => fail e
	}

#[partial]
def use_brace_item_sub (input : String) : ParseResult UseItem :=
	match identifier input {
		success rem name => use_brace_item_sub_items name rem,
		fail e => fail e
	}

#[partial]
def use_brace_item_sub_items (name : String) (input : String) : ParseResult UseItem :=
	match use_brace_items (skip_spaces input) {
		success rem items => success rem (UseItem.use_sub (Identifier.id name) items),
		fail e => fail e
	}

#[partial]
def use_brace_item_sub_rename (input : String) : ParseResult UseItem :=
	match identifier input {
		success rem name => use_brace_item_sub_rename_alias name rem,
		fail e => fail e
	}

#[partial]
def use_brace_item_sub_rename_alias (name : String) (input : String) : ParseResult UseItem :=
	match as_kw (skip_spaces input) {
		success rem _ => match identifier (skip_spaces rem) {
			success rem2 alias => use_brace_item_sub_rename_items name alias rem2,
			fail e => fail e
		},
		fail e => fail e
	}

#[partial]
def use_brace_item_sub_rename_items (name : String) (alias : String) (input : String) : ParseResult UseItem :=
	match use_brace_items (skip_spaces input) {
		success rem items => success rem (UseItem.use_sub_rename (Identifier.id name) (Identifier.id alias) items),
		fail e => fail e
	}

#[partial]
def use_brace_items (input : String) : ParseResult (List UseItem) :=
	delimited_by brace_open (separated_by brace_sep use_brace_item) brace_close input

def use_brace_filter (input : String) : ParseResult UseFilter :=
	map_parse UseFilter.use_items use_brace_items input

/// Optional `{ items }` filter after `use Module`. Absent braces yield
/// `UseFilter.use_bare` (deprecated bare use) without failing the parse.
def use_opt_filter (input : String) : ParseResult UseFilter :=
	let after_ws : String := skip_spaces input in
	match use_brace_filter after_ws {
		success rem filter => success rem filter,
		fail e => success after_ws UseFilter.use_bare
	}

/// `use` has its own binary `pub use` handling rather than the shared
/// `Visibility` type (there's no `priv use` form) — an optional `pub `
/// prefix directly before the `use` keyword.
#[partial]
def use_parser (input : String) : ParseResult Decl :=
	use_try_pub (tag "pub" input) input

#[partial]
def use_try_pub (r : ParseResult String) (orig : String) : ParseResult Decl :=
	match r {
		success rem _ => use_pub_require_ws rem orig,
		fail _ => use_kw (tag "use" orig) false
	}

#[partial]
def use_pub_require_ws (rem : String) (orig : String) : ParseResult Decl :=
	match ws1 rem {
		success rem2 _ => use_kw (tag "use" rem2) true,
		fail _ => use_kw (tag "use" orig) false
	}

#[partial]
def use_kw (r : ParseResult String) (public : Bool) : ParseResult Decl :=
	match r {
		success rem _ => match module_path_parser (skip_spaces rem) {
			success rem2 path => use_after_path path public rem2,
			fail e => fail e
		},
		fail e => fail e
	}

def use_after_path (path : ModulePath) (public : Bool) (input : String) : ParseResult Decl :=
	match use_opt_filter input {
		success rem filter => success rem (Decl.use_d path filter public),
		fail e => fail e
	}

// open module.path [{names}] [in decl]
//
// Optional braces (unlike `use`, still mandatory) restrict `open` to a
// plain identifier list — no glob/rename/sub-module forms. An optional
// trailing `in <decl>` (one of def/class/instance/struct/type) makes the
// open apply only to that one wrapped declaration.

def open_names (input : String) : ParseResult (List Identifier) :=
	map_parse (List.map Identifier.id) (separated_by brace_sep identifier) input

def open_filter_only (input : String) : ParseResult OpenFilter :=
	map_parse OpenFilter.open_only (delimited_by brace_open open_names brace_close) input

def open_opt_filter (input : String) : ParseResult OpenFilter :=
	let after_ws : String := skip_spaces input in
	match open_filter_only after_ws {
		success rem filter => success rem filter,
		fail e => success after_ws OpenFilter.open_all
	}

def in_kw (input : String) : ParseResult String :=
	tag "in" (skip_spaces input)

def scoped_open_inner_decl (input : String) : ParseResult Decl :=
	alt_fold [def_parser, class_parser, instance_parser, struct_parser, type_parser] (skip_spaces input)

#[partial]
def open_parser (input : String) : ParseResult Decl :=
	match tag "open" input {
		success rem _ => match module_path_parser (skip_spaces rem) {
			success rem2 path => open_after_path path rem2,
			fail e => fail e
		},
		fail e => fail e
	}

#[partial]
def open_after_path (path : ModulePath) (input : String) : ParseResult Decl :=
	match open_opt_filter input {
		success rem filter => open_after_filter path filter rem,
		fail e => fail e
	}

#[partial]
def open_after_filter (path : ModulePath) (filter : OpenFilter) (input : String) : ParseResult Decl :=
	match opt (preceded_by in_kw scoped_open_inner_decl) input {
		success rem maybe_decl => success rem (open_build path filter maybe_decl),
		fail e => fail e
	}

def open_build (path : ModulePath) (filter : OpenFilter) (maybe_decl : Option Decl) : Decl :=
	match maybe_decl {
		Option.some decl => Decl.scoped_open_d path filter decl,
		Option.none => Decl.open_d path filter
	}

// infix [:N] (op) := path
//
// The `:N` precedence clause is genuinely optional (parsed and then
// discarded — the resulting Decl.infix_d never records it), so it's
// expressed with `opt` rather than a hand-rolled fail-branch fallback.

def infix_parser (input : String) : ParseResult Decl :=
	match vis_parser input {
		success rem vis => infix_vis rem vis,
		fail e => fail e
	}

def infix_vis (input : String) (vis : Visibility) : ParseResult Decl :=
	match tag "infix" input {
		success rem _ => infix_after_kw rem vis,
		fail e => fail e
	}

def infix_precedence_clause (input : String) : ParseResult I64 :=
	preceded_by infix_colon_tag number input

def infix_colon_tag (input : String) : ParseResult String :=
	tag ":" (skip_spaces input)

def infix_after_kw (input : String) (vis : Visibility) : ParseResult Decl :=
	match opt infix_precedence_clause input {
		success rem _ => infix_paren rem vis,
		fail e => fail e
	}

def infix_paren (input : String) (vis : Visibility) : ParseResult Decl :=
	match tag "(" (skip_spaces input) {
		success rem _ => infix_op rem vis,
		fail e => fail e
	}

def infix_op (input : String) (vis : Visibility) : ParseResult Decl :=
	match operator_parse (skip_spaces input) {
		success rem op => infix_close rem op vis,
		fail e => fail e
	}

def infix_close (input : String) (op : String) (vis : Visibility) : ParseResult Decl :=
	match tag ")" (skip_spaces input) {
		success rem _ => infix_assign rem op vis,
		fail e => fail e
	}

def infix_assign (input : String) (op : String) (vis : Visibility) : ParseResult Decl :=
	match tag ":=" (skip_spaces input) {
		success rem _ => infix_path rem op vis,
		fail e => fail e
	}

def infix_path (input : String) (op : String) (vis : Visibility) : ParseResult Decl :=
	match module_path_parser (skip_spaces input) {
		success rem path => success rem (Decl.infix_d (Operator.operator op) path vis),
		fail e => fail e
	}

// struct Name { field1 : Type, field2 : Type := default }

#[partial]
def struct_parser (input : String) : ParseResult Decl :=
	match vis_parser input {
		success rem vis => struct_vis rem vis,
		fail e => fail e
	}

#[partial]
def struct_vis (input : String) (vis : Visibility) : ParseResult Decl :=
	struct_kw (tag "struct" input) vis

#[partial]
def struct_kw (r : ParseResult String) (vis : Visibility) : ParseResult Decl :=
	match r {
		success rem _ => struct_name (dotted_def_name (skip_spaces rem)) vis,
		fail e => fail e
	}

#[partial]
def struct_name (r : ParseResult String) (vis : Visibility) : ParseResult Decl :=
	match r {
		success rem name => struct_brace (tag "{" (skip_spaces rem)) (Identifier.id name) vis,
		fail e => fail e
	}

#[partial]
def struct_brace (r : ParseResult String) (name : Identifier) (vis : Visibility) : ParseResult Decl :=
	match r {
		success rem _ => struct_fields rem name vis,
		fail e => fail e
	}

#[partial]
def struct_fields (input : String) (name : Identifier) (vis : Visibility) : ParseResult Decl :=
	let empty_ctx : List Identifier := List.empty in
	match separated_by (tag ",") (preceded_by ws0 (struct_one_field empty_ctx)) input {
		success rem fields =>
			match tag "}" (skip_spaces rem) {
				success rem2 _ => success rem2 (Decl.struct_d (Struct.mk name fields vis)),
				fail e => fail (ParseError.custom "expected }" rem)
			},
		fail e => fail e
	}

/// Parse an optional multiplicity-prefix character before a struct
/// field's name — `%` (Zero/Erased), `!` (Linear), `?` (Affine), or none
/// at all (Many, the default). Mirrors the Rust reference's
/// `multiplicity_prefix`. Never fails: an absent prefix is Many, same
/// shape as `vis_parser` always succeeding with a default.
#[partial]
def multiplicity_prefix (input : String) : ParseResult Multiplicity :=
	multiplicity_try_zero (tag "%" input) input

#[partial]
def multiplicity_try_zero (r : ParseResult String) (orig : String) : ParseResult Multiplicity :=
	match r {
		success rem _ => success rem Multiplicity.zero,
		fail _ => multiplicity_try_linear (tag "!" orig) orig
	}

#[partial]
def multiplicity_try_linear (r : ParseResult String) (orig : String) : ParseResult Multiplicity :=
	match r {
		success rem _ => success rem Multiplicity.linear,
		fail _ => multiplicity_try_affine (tag "?" orig) orig
	}

#[partial]
def multiplicity_try_affine (r : ParseResult String) (orig : String) : ParseResult Multiplicity :=
	match r {
		success rem _ => success rem Multiplicity.affine,
		fail _ => success orig Multiplicity.many
	}

#[partial]
def struct_one_field (ctx : List Identifier) (input : String) : ParseResult StructField :=
	match multiplicity_prefix input {
		success rem mult => struct_field_name (identifier rem) ctx mult,
		fail e => fail e
	}

#[partial]
def struct_field_name (r : ParseResult String) (ctx : List Identifier) (mult : Multiplicity) : ParseResult StructField :=
	match r {
		success rem name => struct_field_colon (tag ":" (skip_spaces rem)) (Identifier.id name) ctx mult,
		fail e => fail e
	}

#[partial]
def struct_field_colon (r : ParseResult String) (name : Identifier) (ctx : List Identifier) (mult : Multiplicity) : ParseResult StructField :=
	match r {
		success rem _ => struct_field_type (type_expression ctx (skip_docstrings (skip_spaces rem))) name ctx mult,
		fail e => fail e
	}

#[partial]
def struct_field_type (r : ParseResult Term) (name : Identifier) (ctx : List Identifier) (mult : Multiplicity) : ParseResult StructField :=
	match r {
		success rem typ => struct_field_default (tag ":=" (skip_spaces rem)) rem name typ ctx mult,
		fail e => fail e
	}

#[partial]
def struct_field_default (r : ParseResult String) (orig : String) (name : Identifier) (typ : Term) (ctx : List Identifier) (mult : Multiplicity) : ParseResult StructField :=
	match r {
		success rem _ => struct_field_default_val (expression ctx (skip_docstrings (skip_spaces rem))) name typ mult,
		fail _ =>
			let none : Option Term := Option.none in
			success orig (StructField.mk name typ none mult)
	}

#[partial]
def struct_field_default_val (r : ParseResult Term) (name : Identifier) (typ : Term) (mult : Multiplicity) : ParseResult StructField :=
	match r {
		success rem defval =>
			let some_val : Option Term := Option.some defval in
			success rem (StructField.mk name typ some_val mult),
		fail e => fail e
	}

// type Name { constructor1 (args), constructor2 }
//
// `#[...]` attributes (e.g. `#[derive_cli]`) previously didn't parse at
// all before `type` (unlike `def`, which at least tolerated and
// skipped them) — captured here via `opt_attributes` and patched onto
// the fully-parsed `Decl` afterward, same "placeholder now, patch
// later" shape `def_parser`'s own `def_try_attrs`/`def_apply_attrs`
// use just above.

#[partial]
def type_parser (input : String) : ParseResult Decl :=
	type_try_attrs (opt_attributes input) input

#[partial]
def type_try_attrs (r : ParseResult (List Attribute)) (orig : String) : ParseResult Decl :=
	match r {
		success rem attrs => type_apply_attrs (type_vis_entry rem) attrs,
		fail _ => type_vis_entry orig
	}

#[partial]
def type_vis_entry (input : String) : ParseResult Decl :=
	match vis_parser input {
		success rem vis => type_vis rem vis,
		fail e => fail e
	}

#[partial]
def type_apply_attrs (dr : ParseResult Decl) (attrs : List Attribute) : ParseResult Decl :=
	match dr {
		success rem decl =>
			match decl {
				inductive_d ind =>
					match ind {
						Inductive.mk name params kind cons _ vis =>
							success rem (Decl.inductive_d (Inductive.mk name params kind cons attrs vis))
					},
				_ => success rem decl
			},
		fail e => fail e
	}

#[partial]
def type_vis (input : String) (vis : Visibility) : ParseResult Decl :=
	type_kw (tag "type" input) vis

#[partial]
def type_kw (r : ParseResult String) (vis : Visibility) : ParseResult Decl :=
	match r {
		success rem _ => type_name (dotted_def_name (skip_spaces rem)) vis,
		fail e => fail e
	}

#[partial]
def type_name (r : ParseResult String) (vis : Visibility) : ParseResult Decl :=
	match r {
		success rem name =>
			let empty_params : List Param := List.empty in
			type_params_loop rem (Identifier.id name) empty_params vis,
		fail e => fail e
	}

// Type-level params come in two shapes: bare identifiers (`type Either E
// A {`, kind defaulted to `Type`/Sort 1) and, previously entirely
// unsupported, parenthesized typed params (`type Eq (A : Sort 1) (a : A)
// (b : A) : Prop {`). An optional `: Kind` before `{` (`Prop`/`Sort n`)
// was also unsupported — both blocked `init/prelude.mo`'s `True`/`Eq`
// (a self-hosting-adjacent stdlib file). Both are captured into real
// `Param`/`Term` values now (previously dropped even when the bare-param
// case parsed: `type_to_decl` hardcoded empty params and `Sort 1`).
#[partial]
def type_params_loop (input : String) (name : Identifier) (params : List Param) (vis : Visibility) : ParseResult Decl :=
	type_params_try_bare (identifier (skip_spaces input)) input name params vis

#[partial]
def type_params_try_bare (r : ParseResult String) (orig : String) (name : Identifier) (params : List Param) (vis : Visibility) : ParseResult Decl :=
	match r {
		success rem next => type_params_loop rem name (List.cons (param_many (Identifier.id next) (Term.type_ 1)) params) vis,
		fail _ => type_params_try_paren (tag "(" (skip_spaces orig)) orig name params vis
	}

#[partial]
def type_params_try_paren (r : ParseResult String) (orig : String) (name : Identifier) (params : List Param) (vis : Visibility) : ParseResult Decl :=
	match r {
		success rem _ => type_params_paren_name (identifier (skip_spaces rem)) name params vis,
		fail _ => type_kind_or_brace orig name params vis
	}

#[partial]
def type_params_paren_name (r : ParseResult String) (name : Identifier) (params : List Param) (vis : Visibility) : ParseResult Decl :=
	match r {
		success rem pname => type_params_paren_colon (tag ":" (skip_spaces rem)) pname name params vis,
		fail e => fail e
	}

#[partial]
def type_params_paren_colon (r : ParseResult String) (pname : String) (name : Identifier) (params : List Param) (vis : Visibility) : ParseResult Decl :=
	match r {
		success rem _ =>
			let empty_ctx : List Identifier := List.empty in
			type_params_paren_type (type_expression empty_ctx rem) pname name params vis,
		fail e => fail e
	}

#[partial]
def type_params_paren_type (r : ParseResult Term) (pname : String) (name : Identifier) (params : List Param) (vis : Visibility) : ParseResult Decl :=
	match r {
		success rem typ => type_params_paren_close (tag ")" (skip_spaces rem)) (param_many (Identifier.id pname) typ) name params vis,
		fail e => fail e
	}

#[partial]
def type_params_paren_close (r : ParseResult String) (p : Param) (name : Identifier) (params : List Param) (vis : Visibility) : ParseResult Decl :=
	match r {
		success rem _ => type_params_loop rem name (List.cons p params) vis,
		fail e => fail e
	}

/// After all params: an optional `: Kind` (`Prop`, `Sort n`, ...) before
/// the `{`, defaulting to `Type` (Sort 1) when absent.
#[partial]
def type_kind_or_brace (input : String) (name : Identifier) (params : List Param) (vis : Visibility) : ParseResult Decl :=
	type_try_kind (tag ":" (skip_spaces input)) input name params vis

#[partial]
def type_try_kind (r : ParseResult String) (orig : String) (name : Identifier) (params : List Param) (vis : Visibility) : ParseResult Decl :=
	match r {
		success rem _ =>
			let empty_ctx : List Identifier := List.empty in
			type_kind_expr (type_expression empty_ctx rem) name params vis,
		fail _ => type_brace (tag "{" (skip_spaces orig)) name params (Term.type_ 1) vis
	}

#[partial]
def type_kind_expr (r : ParseResult Term) (name : Identifier) (params : List Param) (vis : Visibility) : ParseResult Decl :=
	match r {
		success rem kind => type_brace (tag "{" (skip_spaces rem)) name params kind vis,
		fail e => fail e
	}

#[partial]
def type_brace (r : ParseResult String) (name : Identifier) (params : List Param) (kind : Term) (vis : Visibility) : ParseResult Decl :=
	match r {
		success rem _ => type_constructors rem name params kind vis,
		fail e => fail e
	}

/// `preceded_by`'s own `before` parser needs a `String -> ParseResult
/// String` shape (matching `ws0`'s), so a comment-aware skip can't be
/// spliced in as bare `skip_docstrings (skip_spaces ...)` (a plain
/// `String -> String`) the way every OTHER site in this file does --
/// this wraps it to fit. Fixes a doc comment between two constructor
/// variants (`type X { a (...), /// doc\n b (...) }`) breaking the
/// whole type declaration -- same underlying comment-skip gap as
/// `match_case_arrow`/`if_then_branch`/etc. elsewhere in this file, just
/// needing a different shape here since `type_constructors` goes
/// through the generic `separated_by`/`preceded_by` combinators instead
/// of a hand-written per-branch chain.
#[partial]
def ws0_and_comments (input : String) : ParseResult String :=
	success (skip_docstrings (skip_spaces input)) input

#[partial]
def type_constructors (input : String) (name : Identifier) (params : List Param) (kind : Term) (vis : Visibility) : ParseResult Decl :=
	let empty_ctx : List Identifier := List.empty in
	match separated_by (tag ",") (preceded_by ws0_and_comments (type_one_constructor empty_ctx)) input {
		success rem cons =>
			match tag "}" (skip_docstrings (skip_spaces rem)) {
				success rem2 _ => success rem2 (type_to_decl name (list_reverse params) kind cons vis),
				fail e => fail (ParseError.custom "expected }" rem)
			},
		fail e => fail e
	}

#[partial]
def type_one_constructor (ctx : List Identifier) (input : String) : ParseResult InductConstructor :=
	type_cons_name (identifier input) ctx

#[partial]
def type_cons_name (r : ParseResult String) (ctx : List Identifier) : ParseResult InductConstructor :=
	match r {
		success rem name => type_cons_try_gadt (tag ":" (skip_spaces rem)) rem (Identifier.id name) ctx,
		fail e => fail e
	}

/// GADT-style constructor: `name : FullType` (e.g. `refl : Eq A a a` in
/// `init/prelude.mo`'s `Eq` type), as opposed to `name (args)`/bare
/// `name`. Tried first since a real `(`/bare-field constructor never has
/// `:` directly after its name.
#[partial]
def type_cons_try_gadt (r : ParseResult String) (orig : String) (name : Identifier) (ctx : List Identifier) : ParseResult InductConstructor :=
	match r {
		success rem _ =>
			let empty_ctx : List Identifier := List.empty in
			type_cons_gadt_type (type_expression empty_ctx rem) name,
		fail _ => type_cons_paren_or_nil (tag "(" (skip_spaces orig)) orig name ctx
	}

#[partial]
def type_cons_gadt_type (r : ParseResult Term) (name : Identifier) : ParseResult InductConstructor :=
	match r {
		success rem typ =>
			let empty_params : List Param := List.empty in
			success rem (InductConstructor.mk (ModulePath.mp (List.cons name List.empty)) empty_params typ),
		fail e => fail e
	}

// Constructor field parsing needs to support all of: a bare unnamed type
// with no parens at all (`io A`, `tag String`), a single parenthesized
// unnamed type (`mp (List Identifier)`), one-or-more comma-separated
// named-or-bare fields within a group (`mk (a: A, b: B)`), and — the
// dominant style throughout lang/types.mo itself, 42+ uses — MULTIPLE
// separate curried `(...)` groups (`mk (a: A) (b: B) (c: C)`). Previously
// only a single named-field group (`some (a: A)`) was supported; anything
// else left trailing text unconsumed and hard-failed the whole `type`
// declaration (a self-hosting blocker: lang/types.mo and
// lang/parser/core.mo's own foundational types use exactly these shapes).
#[partial]
def type_cons_paren_or_nil (r : ParseResult String) (orig : String) (name : Identifier) (ctx : List Identifier) : ParseResult InductConstructor :=
	match r {
		success rem _ => type_cons_one_group_content rem name ctx List.empty,
		fail _ => type_cons_bare_or_implicit orig name ctx
	}

/// No `(` at all right after the constructor name — try a single bare
/// unnamed type (`io A`), then fall back to the existing `{implicit}`
/// handling, then (via that chain's own fallback) a zero-arg constructor.
#[partial]
def type_cons_bare_or_implicit (orig : String) (name : Identifier) (ctx : List Identifier) : ParseResult InductConstructor :=
	type_cons_try_bare (type_expression ctx orig) orig name ctx

#[partial]
def type_cons_try_bare (r : ParseResult Term) (orig : String) (name : Identifier) (ctx : List Identifier) : ParseResult InductConstructor :=
	match r {
		success rem typ =>
			let p : Param := param_many (Identifier.id "_") typ in
			success rem (InductConstructor.mk (ModulePath.mp (List.cons name List.empty)) (List.cons p List.empty) (Term.hole)),
		fail _ => type_cons_implicit (tag "{" (skip_spaces orig)) orig name ctx
	}

/// Parse one field inside an already-open `(...)` group: named (`a: A`,
/// possibly MULTIPLE names sharing one type — `(b0 b1 ... b15 : List
/// (Pair K V))`, `std/map.mo`'s `Buckets16` constructor — or bare/
/// unnamed (`List Identifier`). Multi-name support here mirrors
/// `def_explicit_more_names`'s already-fixed shape for `def` params;
/// this constructor-field path had its own separate (and, until now,
/// single-name-only) implementation.
#[partial]
def type_cons_one_group_content (input : String) (name : Identifier) (ctx : List Identifier) (params : List Param) : ParseResult InductConstructor :=
	let cleaned : String := skip_spaces input in
	type_cons_group_name (identifier cleaned) cleaned name ctx params

#[partial]
def type_cons_group_name (r : ParseResult String) (orig : String) (name : Identifier) (ctx : List Identifier) (params : List Param) : ParseResult InductConstructor :=
	match r {
		success rem pname =>
			let names : List Identifier := List.cons (Identifier.id pname) List.empty in
			type_cons_group_more_names rem name ctx params names orig,
		fail _ => type_cons_group_bare (type_expression ctx orig) orig name ctx params
	}

/// After the first field name, try more space-separated names sharing
/// one type before requiring `:` — see `type_cons_one_group_content`'s
/// doc comment. `field_start` is threaded through unchanged all the way
/// from BEFORE the first name was even parsed — needed so
/// `type_cons_group_colon` can backtrack all the way there (not just to
/// the position after the last collected name) if no `:` ever turns up:
/// a bare/unnamed field whose type is itself a multi-identifier
/// application (`map (Buckets16 K V)`, no field name or colon at all)
/// looks EXACTLY like "several field names with no type" until the
/// colon check fails — at which point the only correct move is to
/// re-parse the whole thing from `field_start` as a bare type
/// expression, not hard-fail (that regressed `std/map.mo`'s `HashMap`
/// constructor, whose sole field is exactly this shape).
#[partial]
def type_cons_group_more_names (input : String) (name : Identifier) (ctx : List Identifier) (params : List Param) (names : List Identifier) (field_start : String) : ParseResult InductConstructor :=
	type_cons_group_more_names_try (identifier (skip_spaces input)) input name ctx params names field_start

#[partial]
def type_cons_group_more_names_try (r : ParseResult String) (orig : String) (name : Identifier) (ctx : List Identifier) (params : List Param) (names : List Identifier) (field_start : String) : ParseResult InductConstructor :=
	match r {
		success rem pname => type_cons_group_more_names rem name ctx params (List.cons (Identifier.id pname) names) field_start,
		fail _ => type_cons_group_colon (tag ":" (skip_spaces orig)) name ctx params names field_start
	}

#[partial]
def type_cons_group_colon (r : ParseResult String) (name : Identifier) (ctx : List Identifier) (params : List Param) (names : List Identifier) (field_start : String) : ParseResult InductConstructor :=
	match r {
		success rem _ => type_cons_group_type (type_expression ctx (skip_docstrings (skip_spaces rem))) name ctx params names,
		fail _ => type_cons_group_bare (type_expression ctx field_start) field_start name ctx params
	}

/// Builds one `Param` per name (all sharing `typ`) directly onto the
/// OUTER field accumulator `params` via the shared `params_for_names`
/// helper — `names` (most-recent-first, reversed here back to
/// declaration order) combined with `params_for_names`'s own "cons onto
/// whatever accumulator it's given" behavior means this correctly
/// interleaves with fields from other groups without a separate merge
/// step.
#[partial]
def type_cons_group_type (r : ParseResult Term) (name : Identifier) (ctx : List Identifier) (params : List Param) (names : List Identifier) : ParseResult InductConstructor :=
	match r {
		success rem typ =>
			let new_params : List Param := params_for_names (list_reverse names) typ params in
			type_cons_group_after_item rem name ctx new_params,
		fail e => fail e
	}

#[partial]
def type_cons_group_bare (r : ParseResult Term) (orig : String) (name : Identifier) (ctx : List Identifier) (params : List Param) : ParseResult InductConstructor :=
	match r {
		success rem typ =>
			let p : Param := param_many (Identifier.id "_") typ in
			type_cons_group_after_item rem name ctx (List.cons p params),
		fail e => fail e
	}

/// After one field: another comma-separated field in the SAME group, or
/// the group's closing `)`.
#[partial]
def type_cons_group_after_item (input : String) (name : Identifier) (ctx : List Identifier) (params : List Param) : ParseResult InductConstructor :=
	type_cons_group_try_comma (tag "," (skip_spaces input)) input name ctx params

#[partial]
def type_cons_group_try_comma (r : ParseResult String) (orig : String) (name : Identifier) (ctx : List Identifier) (params : List Param) : ParseResult InductConstructor :=
	match r {
		success rem _ => type_cons_one_group_content (skip_spaces rem) name ctx params,
		fail _ => type_cons_group_close orig name ctx params
	}

#[partial]
def type_cons_group_close (input : String) (name : Identifier) (ctx : List Identifier) (params : List Param) : ParseResult InductConstructor :=
	type_cons_group_close_try (tag ")" (skip_spaces input)) input name ctx params

#[partial]
def type_cons_group_close_try (r : ParseResult String) (orig : String) (name : Identifier) (ctx : List Identifier) (params : List Param) : ParseResult InductConstructor :=
	match r {
		success rem _ => type_cons_more_groups rem name ctx params,
		fail _ => fail (ParseError.custom "expected , or ) in constructor fields" orig)
	}

/// After a group closes: another curried `(...)` group, or done.
#[partial]
def type_cons_more_groups (input : String) (name : Identifier) (ctx : List Identifier) (params : List Param) : ParseResult InductConstructor :=
	type_cons_try_next_group (tag "(" (skip_spaces input)) input name ctx params

#[partial]
def type_cons_try_next_group (r : ParseResult String) (orig : String) (name : Identifier) (ctx : List Identifier) (params : List Param) : ParseResult InductConstructor :=
	match r {
		success rem _ => type_cons_one_group_content rem name ctx params,
		fail _ => type_cons_try_return_type orig name ctx params
	}

/// After all of a constructor's `(...)` param groups: an optional
/// GADT-style trailing `: ReturnType` (`cons (a : A) (List A) : List
/// A`, init/prelude.mo's own `List` -- previously this was always
/// Term.hole here regardless, leaving `: List A` unconsumed, which
/// hard-failed the enclosing `type` declaration's own closing-`}`
/// check). Falls back to Term.hole (the prior, still-correct behavior
/// for the common case of no explicit return type at all) whenever
/// there's no `:` here, or what follows it isn't a valid type
/// expression.
#[partial]
def type_cons_try_return_type (orig : String) (name : Identifier) (ctx : List Identifier) (params : List Param) : ParseResult InductConstructor :=
	match tag ":" (skip_spaces orig) {
		success rem _ => type_cons_return_type (type_expression ctx (skip_docstrings (skip_spaces rem))) orig name params,
		fail _ => success orig (InductConstructor.mk (ModulePath.mp (List.cons name List.empty)) (list_reverse params) (Term.hole))
	}

#[partial]
def type_cons_return_type (r : ParseResult Term) (orig : String) (name : Identifier) (params : List Param) : ParseResult InductConstructor :=
	match r {
		success rem typ => success rem (InductConstructor.mk (ModulePath.mp (List.cons name List.empty)) (list_reverse params) typ),
		fail _ => success orig (InductConstructor.mk (ModulePath.mp (List.cons name List.empty)) (list_reverse params) (Term.hole)),
	}

#[partial]
def type_cons_implicit (r : ParseResult String) (orig : String) (name : Identifier) (ctx : List Identifier) : ParseResult InductConstructor :=
	match r {
		success rem _ => type_cons_implicit_skip (take_while is_not_close_curly rem) rem orig name ctx,
		fail _ =>
			let empty_params : List Param := List.empty in
			success orig (InductConstructor.mk (ModulePath.mp (List.cons name List.empty)) empty_params (Term.hole))
	}

#[partial]
def type_cons_implicit_skip (r : ParseResult String) (rem : String) (orig : String) (name : Identifier) (ctx : List Identifier) : ParseResult InductConstructor :=
	match r {
		success after_bracket _ => type_cons_implicit_close (tag "}" (skip_spaces after_bracket)) after_bracket orig name ctx,
		fail _ =>
			let empty_params : List Param := List.empty in
			success orig (InductConstructor.mk (ModulePath.mp (List.cons name List.empty)) empty_params (Term.hole))
	}

#[partial]
def type_cons_implicit_close (r : ParseResult String) (after_bracket : String) (orig : String) (name : Identifier) (ctx : List Identifier) : ParseResult InductConstructor :=
	match r {
		success rem _ => type_cons_paren_or_nil (tag "(" (skip_spaces rem)) rem name ctx,
		fail _ =>
			let empty_params : List Param := List.empty in
			success after_bracket (InductConstructor.mk (ModulePath.mp (List.cons name List.empty)) empty_params (Term.hole))
	}


#[partial]
def type_to_decl (name : Identifier) (params : List Param) (kind : Term) (cons : List InductConstructor) (vis : Visibility) : Decl :=
	let empty_attrs : List Attribute := List.empty in
	Decl.inductive_d (Inductive.mk (ModulePath.mp (List.cons name List.empty)) params kind cons empty_attrs vis)

/// Optional `pub `/`priv ` prefix before a declaration keyword (parsed
/// after any attributes) — defaults to `Visibility.package_private` when
/// absent. Mirrors the Rust reference's `vis_parser` exactly, including
/// requiring trailing whitespace after the keyword itself (via `ws1`) so
/// `pub`/`priv` as a genuine identifier prefix — e.g. a hypothetical
/// `public`/`privateName` def — isn't misread as the keyword; on that
/// mismatch this backs off to `orig` (the untouched pre-attempt position)
/// and reports `package_private`, letting the caller's own keyword tag
/// (`def`/`type`/...) fail normally against the real, un-consumed text.
/// Applies to `def`/`type`(inductive)/`class`/`struct`/`instance`/
/// `infix` — NOT `use` (own separate `pub`-prefix handling, since `priv
/// use` isn't a real form) or `open` (no visibility concept at all).
#[partial]
def vis_parser (input : String) : ParseResult Visibility :=
	vis_try_pub (tag "pub" input) input

#[partial]
def vis_try_pub (r : ParseResult String) (orig : String) : ParseResult Visibility :=
	match r {
		success rem _ => vis_require_ws rem Visibility.pub_ orig,
		fail _ => vis_try_priv (tag "priv" orig) orig
	}

#[partial]
def vis_try_priv (r : ParseResult String) (orig : String) : ParseResult Visibility :=
	match r {
		success rem _ => vis_require_ws rem Visibility.priv_ orig,
		fail _ => success orig Visibility.package_private
	}

#[partial]
def vis_require_ws (rem : String) (v : Visibility) (orig : String) : ParseResult Visibility :=
	match ws1 rem {
		success rem2 _ => success rem2 v,
		fail _ => success orig Visibility.package_private
	}

// def [#attrs] name {implicit} (explicit) : ret_type := body
// `#[...]` attributes are now captured for real via `opt_attributes`
// (see that function's own doc comment above) rather than skipped —
// `def_try_attrs` captures them once at the very start, then
// `def_apply_attrs` patches them onto the already-fully-parsed `Decl`
// afterward, exactly mirroring `def_apply_constraints`'s own
// "placeholder now, patch later" pattern just below (see ITS doc
// comment for why: avoids threading a new accumulator through the
// whole `def_params`/`def_body`/... chain down to `def_to_decl`).

#[partial]
def def_parser (input : String) : ParseResult Decl :=
	def_try_attrs (opt_attributes input) input

#[partial]
def def_try_attrs (r : ParseResult (List Attribute)) (orig : String) : ParseResult Decl :=
	match r {
		success rem attrs => def_apply_attrs (def_vis_done (vis_parser (skip_spaces rem))) attrs,
		fail _ => def_vis_done (vis_parser (skip_spaces orig))
	}

/// Patch the real attrs onto the fully-parsed `Decl` — see
/// `def_try_attrs`'s doc comment above. `attrs` is `List.empty` for
/// the overwhelming majority of defs (no `#[...]` present at all —
/// `opt_attributes` always succeeds, even with zero attributes found),
/// so this only ever changes the constructed `Def`'s `attrs` field
/// away from its own already-`List.empty` default when there really
/// was one.
#[partial]
def def_apply_attrs (dr : ParseResult Decl) (attrs : List Attribute) : ParseResult Decl :=
	match dr {
		success rem decl =>
			match decl {
				def_d d =>
					match d {
						Def.mk name typ term constraints _ vis =>
							success rem (Decl.def_d (Def.mk name typ term constraints attrs vis))
					},
				_ => success rem decl
			},
		fail e => fail e
	}

/// `vis_parser` never itself fails (defaults to `package_private`), so
/// this always takes the success branch — matches the shape every other
/// `Result`-consuming step in this parser uses, no special case needed.
#[partial]
def def_vis_done (r : ParseResult Visibility) : ParseResult Decl :=
	match r {
		success rem vis => def_kw (tag "def" (skip_spaces rem)) vis,
		fail e => fail e
	}

#[partial]
def def_kw (r : ParseResult String) (vis : Visibility) : ParseResult Decl :=
	match r {
		success rem _ => def_name (dotted_def_name (skip_spaces rem)) vis,
		fail e => fail e
	}

/// A def's name, e.g. `foo` or the very common method-style
/// `Option.get_or_default`/`IO.println`. `def_name` previously parsed
/// this with a bare `identifier`, which stops at the first `.` — every
/// dotted def name in the codebase (the norm for method-style stdlib
/// functions) failed to parse as a result. That failure used to be
/// silently swallowed by `decls_try`'s old truncate-on-fail behavior, so
/// it went unnoticed until real files were loaded end-to-end.
#[partial]
def dotted_def_name (input : String) : ParseResult String :=
	map_parse join_dotted_identifiers dotted_identifier input

#[partial]
def def_name (r : ParseResult String) (vis : Visibility) : ParseResult Decl :=
	match r {
		success rem name => def_try_constraints (tag "[" (skip_spaces rem)) (skip_spaces rem) (Identifier.id name) vis,
		fail e => fail e
	}

/// A `def`-level `[Constraint A, ...]` clause between the name and its
/// params (real usage: `std/map.mo`'s `def BTreeMap.beq [BEq K, BEq V]
/// (a b : BTreeMap K V) : Bool := ...`) — previously entirely
/// unsupported (`class`/`instance`/`type` all already had their own
/// `[...]` constraint parsing, `def` never did). Patches the parsed
/// constraints onto the fully-parsed `Decl` afterward via
/// `def_apply_constraints`, the same "placeholder now, patch later"
/// pattern already used by `class`/`instance` (`def_to_decl` keeps
/// hardcoding an empty constraint list as that placeholder) — avoids
/// threading a new accumulator through the whole `def_params`/
/// `def_body`/... chain down to `def_to_decl`.
#[partial]
def def_try_constraints (r : ParseResult String) (orig : String) (name : Identifier) (vis : Visibility) : ParseResult Decl :=
	match r {
		success rem _ => def_constraints_content (take_while is_not_bracket rem) rem name vis,
		fail _ => def_params_entry orig name vis
	}

#[partial]
def def_constraints_content (r : ParseResult String) (orig : String) (name : Identifier) (vis : Visibility) : ParseResult Decl :=
	match r {
		success rem content => def_constraints_then_close (type_constraint_list content) rem name vis,
		fail _ => fail (ParseError.custom "expected ]" orig)
	}

#[partial]
def def_constraints_then_close (cr : ParseResult (List TypeConstraint)) (input : String) (name : Identifier) (vis : Visibility) : ParseResult Decl :=
	match cr {
		success _ constraints => def_constraints_close_bracket (tag "]" input) constraints name vis,
		fail _ =>
			let empty_cs : List TypeConstraint := List.empty in
			def_constraints_close_bracket (tag "]" input) empty_cs name vis
	}

#[partial]
def def_constraints_close_bracket (r : ParseResult String) (constraints : List TypeConstraint) (name : Identifier) (vis : Visibility) : ParseResult Decl :=
	match r {
		success rem _ => def_apply_constraints (def_params_entry (skip_spaces rem) name vis) constraints,
		fail e => fail (ParseError.custom "expected ] after def constraint" (parse_error_remaining e))
	}

#[partial]
def def_params_entry (input : String) (name : Identifier) (vis : Visibility) : ParseResult Decl :=
	let empty : List Param := List.empty in
	def_params (def_params_loop input empty) name vis

/// Patch the real constraints onto the fully-parsed `Decl` — see
/// `def_try_constraints`'s doc comment above.
#[partial]
def def_apply_constraints (dr : ParseResult Decl) (constraints : List TypeConstraint) : ParseResult Decl :=
	match dr {
		success rem decl =>
			match decl {
				def_d d =>
					match d {
						Def.mk name typ term _ attrs vis =>
							success rem (Decl.def_d (Def.mk name typ term constraints attrs vis))
					},
				_ => success rem decl
			},
		fail e => fail e
	}

#[partial]
def def_params_loop (input : String) (params : List Param) : ParseResult (List Param) :=
	def_params_try_implicit (tag "{" input) input params

#[partial]
def def_params_try_implicit (r : ParseResult String) (orig : String) (params : List Param) : ParseResult (List Param) :=
	match r {
		success rem _ => def_implicit_param (identifier (skip_spaces rem)) rem params,
		fail _ => def_params_try_explicit (tag "(" orig) orig params
	}

#[partial]
def def_implicit_param (r : ParseResult String) (rem : String) (params : List Param) : ParseResult (List Param) :=
	match r {
		success rem2 name => def_implicit_more_names rem2 rem name params,
		fail e => fail e
	}

/// After the first name in a `{...}` implicit-param clause, try more
/// space-separated names sharing one type (`{K V : Type}`, not just
/// `{K : Type} {V : Type}`) — same shape as the already-fixed explicit
/// `(a b : Type)` case. The clause's parsed content is discarded either
/// way (see `def_implicit_close`'s doc comment) so, unlike the explicit
/// case, there's no need to build a `Param` per name here — just consume
/// the right amount of text so multi-name clauses parse instead of
/// hard-failing on the second name.
#[partial]
def def_implicit_more_names (input : String) (brace_rem : String) (name : String) (params : List Param) : ParseResult (List Param) :=
	def_implicit_more_names_try (identifier (skip_spaces input)) input brace_rem name params

#[partial]
def def_implicit_more_names_try (r : ParseResult String) (orig : String) (brace_rem : String) (name : String) (params : List Param) : ParseResult (List Param) :=
	match r {
		success rem2 _ => def_implicit_more_names rem2 brace_rem name params,
		fail _ => def_implicit_colon (tag ":" (skip_spaces orig)) brace_rem orig name params
	}

#[partial]
def def_implicit_colon (r : ParseResult String) (brace_rem : String) (rem : String) (name : String) (params : List Param) : ParseResult (List Param) :=
	match r {
		success rem2 _ =>
			let empty_ctx : List Identifier := List.empty in
			def_implicit_type (type_expression empty_ctx rem2) brace_rem rem name params,
		fail e => fail e
	}

#[partial]
def def_implicit_type (r : ParseResult Term) (brace_rem : String) (rem : String) (name : String) (params : List Param) : ParseResult (List Param) :=
	match r {
		success rem2 typ => def_implicit_close (tag "}" rem2) brace_rem name typ params,
		fail e => fail e
	}

/// Closes a `{name : type}` implicit-param clause. On success this
/// deliberately drops `name`/`typ` and restarts `params` from empty,
/// rather than adding the clause's binding(s) to the accumulated list —
/// not a bug: `lang/elaborate.mo`'s `elaborate_def`/`wrap_forall` already
/// auto-wraps any free type variable appearing elsewhere in the def's
/// signature into an implicit forall regardless of whether the user wrote
/// it explicitly, so an explicit `{A : Type}` clause and omitting it
/// entirely elaborate to the identical final type. The clause still has
/// to *parse* correctly (as documentation/DX, and so the def's remaining
/// signature/body are found at the right offset) even though its content
/// doesn't need to survive into the parsed `Param` list.
#[partial]
def def_implicit_close (r : ParseResult String) (brace_rem : String) (name : String) (typ : Term) (params : List Param) : ParseResult (List Param) :=
	match r {
		success rem2 _ =>
			let empty : List Param := List.empty in
			def_params_loop (skip_spaces rem2) empty,
		fail e => fail e
	}

#[partial]
def def_params_try_explicit (r : ParseResult String) (orig : String) (params : List Param) : ParseResult (List Param) :=
	match r {
		// `opt_attributes` captured right after the opening `(` -- the
		// one real per-param attribute shape (`#[arg]`, e.g.
		// `(#[arg] verbose : Bool)` in a #[derive_cli]-annotated type's
		// constructor) is on a CONSTRUCTOR field, not a `def` param
		// (see lang/tests/cli_derive_tests.mo, deliberately Rust-host-
		// only per its own doc comment) -- so this specific path has no
		// in-scope real corpus target, unlike every other piece of this
		// plan. Lower-confidence, hand-repro-only per
		// plans/bootstrapping/self-hosted-compiler.md's own staging.
		success rem _ => def_explicit_attrs (opt_attributes rem) rem params,
		fail _ =>
			let rev : List Param := list_reverse params in
			success orig rev
	}

#[partial]
def def_explicit_attrs (r : ParseResult (List Attribute)) (close_rem : String) (params : List Param) : ParseResult (List Param) :=
	match r {
		success rem attrs => def_explicit_param (identifier (skip_spaces rem)) close_rem params attrs,
		fail e => fail e
	}

#[partial]
def def_explicit_param (r : ParseResult String) (close_rem : String) (params : List Param) (attrs : List Attribute) : ParseResult (List Param) :=
	match r {
		success rem name => def_explicit_more_names rem close_rem (List.cons (Identifier.id name) List.empty) params attrs,
		fail e => fail e
	}

/// After the first param name, try to parse MORE space-separated names
/// sharing one type before requiring `:` — supports `(a b : Type)`, the
/// dominant shape for binary functions throughout the stdlib, not just
/// `(a : Type) (b : Type)`. `names` accumulates most-recently-parsed-first
/// (reverse declaration order), mirroring how `params` itself accumulates.
#[partial]
def def_explicit_more_names (input : String) (close_rem : String) (names : List Identifier) (params : List Param) (attrs : List Attribute) : ParseResult (List Param) :=
	def_explicit_more_names_try (identifier (skip_spaces input)) input close_rem names params attrs

#[partial]
def def_explicit_more_names_try (r : ParseResult String) (orig : String) (close_rem : String) (names : List Identifier) (params : List Param) (attrs : List Attribute) : ParseResult (List Param) :=
	match r {
		success rem name => def_explicit_more_names rem close_rem (List.cons (Identifier.id name) names) params attrs,
		fail _ => def_explicit_colon (tag ":" (skip_spaces orig)) close_rem names params attrs
	}

#[partial]
def def_explicit_colon (r : ParseResult String) (close_rem : String) (names : List Identifier) (params : List Param) (attrs : List Attribute) : ParseResult (List Param) :=
	match r {
		success rem _ =>
			let empty_ctx : List Identifier := List.empty in
			def_explicit_type (type_expression empty_ctx rem) close_rem names params attrs,
		fail e => fail e
	}

#[partial]
def def_explicit_type (r : ParseResult Term) (close_rem : String) (names : List Identifier) (params : List Param) (attrs : List Attribute) : ParseResult (List Param) :=
	match r {
		success rem typ => def_explicit_close (tag ")" rem) close_rem names typ params attrs,
		fail e => fail e
	}

#[partial]
def def_explicit_close (r : ParseResult String) (close_rem : String) (names : List Identifier) (typ : Term) (params : List Param) (attrs : List Attribute) : ParseResult (List Param) :=
	match r {
		success rem _ => def_params_loop (skip_spaces rem) (params_for_names_attrs (list_reverse names) typ attrs params),
		fail e => fail e
	}

/// Build one `Param` per name (all sharing `typ`), consing each onto
/// `params` in declaration order — `names` must already be in original
/// left-to-right order (i.e. pre-reversed by the caller), matching the
/// existing "most-recent-first, reversed once at the very end" invariant
/// `params` itself follows throughout this parser.
#[partial]
def params_for_names (names : List Identifier) (typ : Term) (params : List Param) : List Param := match names {
	List.empty => params,
	List.cons n rest => params_for_names rest typ (List.cons (param_many n typ) params),
}

/// Sibling to `params_for_names` used only by the explicit-param chain
/// above (which now always has a captured `attrs` list, possibly
/// empty) — applies `attrs` to every `Param` built from this one
/// `(...)` group. Deliberately NOT merged into `params_for_names`
/// itself: `def`'s own `{implicit}` params and `instance`'s implicit-
/// param chain (`instance_implicit_params_loop`) both go through
/// `params_for_names` directly and never need `#[arg]`-style attrs —
/// threading an always-empty extra parameter through those two other
/// call sites for no benefit isn't worth it. All names in a shared-type
/// group get the SAME attrs if attributed — untested design choice
/// (no real corpus example combines `#[arg]` with a multi-name group
/// either way).
#[partial]
def params_for_names_attrs (names : List Identifier) (typ : Term) (attrs : List Attribute) (params : List Param) : List Param := match names {
	List.empty => params,
	List.cons n rest =>
		let none : Option Term := Option.none in
		params_for_names_attrs rest typ attrs (List.cons (Param.mk n typ Multiplicity.many none attrs) params),
}

#[partial]
def def_params (r : ParseResult (List Param)) (name : Identifier) (vis : Visibility) : ParseResult Decl :=
	match r {
		success rem params => def_ret_type (tag ":" (skip_spaces rem)) rem name params vis,
		fail e => fail e
	}

#[partial]
def def_ret_type (r : ParseResult String) (orig : String) (name : Identifier) (params : List Param) (vis : Visibility) : ParseResult Decl :=
	match r {
		success rem _ =>
			let empty_ctx : List Identifier := List.empty in
			def_ret_expr (type_expression empty_ctx rem) name params vis,
		fail _ => fail (ParseError.custom "expected : return type" orig)
	}

#[partial]
def def_ret_expr (r : ParseResult Term) (name : Identifier) (params : List Param) (vis : Visibility) : ParseResult Decl :=
	match r {
		success rem typ => def_body rem name params typ vis,
		fail e => fail e
	}

#[partial]
def def_body (input : String) (name : Identifier) (params : List Param) (typ : Term) (vis : Visibility) : ParseResult Decl :=
	def_body_assign (tag ":=" (skip_spaces input)) name params typ vis input

#[partial]
def def_body_assign (r : ParseResult String) (name : Identifier) (params : List Param) (typ : Term) (vis : Visibility) (orig : String) : ParseResult Decl :=
	match r {
		// type_expression, not plain expression -- a def's value can
		// itself be a type-level Pi-arrow chain used as a value (a type
		// synonym: `def Lens ... : Type := (A -> F B) -> S -> F T`,
		// init/prelude.mo). type_expression is a strict superset of
		// expression here: it falls through to plain `expression`
		// (type_plain) whenever the dependent-paren-binder form doesn't
		// apply, then ALSO checks for a trailing `->` that expression
		// alone never looks for (`->` isn't a general value-level infix
		// operator, so expression's own operator-precedence climbing
		// correctly backtracks over it, leaving it unconsumed) --
		// ordinary value defs with no top-level `->` parse identically
		// either way. Previously `Lens` parsed as SUCCESS but silently
		// left `-> S -> F T` unconsumed, which decls_try's lenient
		// truncate-on-failure then hit as a bogus "next declaration"
		// starting with `->`, truncating everything after it (including
		// List.last, further down the same file).
		// `skip_docstrings (skip_spaces rem)`, not bare `skip_spaces rem`
		// -- a comment directly after `:=`, before a def's body expression,
		// must be skipped like whitespace here too (same comment-skip fix
		// applied throughout this file's `if`/`match`-arm/do-block entry
		// points).
		success rem _ => def_body_expr (type_expression (ctx_of_params params) (skip_docstrings (skip_spaces rem))) name params typ vis,
		fail _ => def_body_block_or_none (tag "{" (skip_spaces orig)) name params typ vis orig
	}

#[partial]
def def_body_block_or_none (r : ParseResult String) (name : Identifier) (params : List Param) (typ : Term) (vis : Visibility) (orig : String) : ParseResult Decl :=
	match r {
		success rem _ => def_body_do (do_stmts (ctx_of_params params) rem) name params typ vis,
		fail _ => success orig (def_to_decl (lam_params params (Term.hole)) name (build_param_pi_chain params typ) vis)
	}

/// The body is correctly wrapped in one lambda per param via `lam_params`,
/// but the DECLARED type (`typ`, just the bare return-type expression at
/// this point) was previously stored as-is on the `Def`, silently
/// dropping every param's type — e.g. `def add (a b : I64) : I64 := ...`
/// would store type `I64` alone, not `I64 -> I64 -> I64`. Independent of
/// (and predating) the multi-name param parsing fix — this affected every
/// top-level `def` with any explicit params, not just multi-name ones;
/// unreached in practice because nothing exercised a real def's `.typ`
/// field via the self-hosted parser specifically until now. `typecheck`
/// callers need this: `type_check` is handed `Def.typ` as the expected
/// type for `Def.term`, and a lambda-bodied term can only check against
/// a matching Pi-typed expectation.
#[partial]
def def_body_expr (r : ParseResult Term) (name : Identifier) (params : List Param) (typ : Term) (vis : Visibility) : ParseResult Decl :=
	match r {
		success rem body => success rem (def_to_decl (lam_params params body) name (build_param_pi_chain params typ) vis),
		fail e => fail e
	}

#[partial]
def def_body_block (r : ParseResult String) (name : Identifier) (params : List Param) (typ : Term) (vis : Visibility) : ParseResult Decl :=
	match r {
		success rem _ => def_body_do (do_stmts (ctx_of_params params) rem) name params typ vis,
		fail e => fail e
	}

#[partial]
def def_body_do (r : ParseResult (List DoStmt)) (name : Identifier) (params : List Param) (typ : Term) (vis : Visibility) : ParseResult Decl :=
	match r {
		success rem stmts => success rem (def_to_decl (lam_params params (desugar_do stmts)) name (build_param_pi_chain params typ) vis),
		fail e => fail e
	}

// ---------- TypeConstraint parser ----------

#[partial]
def type_constraint_one (input : String) : ParseResult TypeConstraint :=
	type_constraint_one_name (module_path_parser input) input

#[partial]
def type_constraint_one_name (r : ParseResult ModulePath) (orig : String) : ParseResult TypeConstraint :=
	match r {
		success rem cls =>
			let empty_vars : List Identifier := List.empty in
			type_constraint_vars (take_while is_ident_char (skip_spaces rem)) cls empty_vars rem,
		fail _ => fail (ParseError.custom "expected class name in constraint" orig)
	}

#[partial]
def type_constraint_vars (r : ParseResult String) (cls : ModulePath) (acc : List Identifier) (orig : String) : ParseResult TypeConstraint :=
	match r {
		success rest ident =>
			if is_empty ident
			then success rest (TypeConstraint.mk cls (list_reverse acc))
			else type_constraint_vars (take_while is_ident_char (skip_spaces rest)) cls (List.cons (Identifier.id ident) acc) orig,
		fail _ => success orig (TypeConstraint.mk cls (list_reverse acc))
	}

#[partial]
def type_constraint_list (input : String) : ParseResult (List TypeConstraint) :=
    separated_by (tag ",") (preceded_by ws0 type_constraint_one) input

// class [constraints] Name params { def method sig, def method sig := default }
//
// A long continuation chain (class_kw -> ... -> class_close below) because
// each grammar choice point needs its own function: optional `[...]`
// constraints before the name, then the class's own type params (either
// bare identifiers or one-or-more parenthesized groups — class_params
// through class_try_more_parens_or_brace), then a brace-delimited list of
// methods where each method is `def name (params) : ret_type [:=
// default_body]` with its own multi-step param-list and optional
// default-value parsing (class_methods/class_methods_single loop over
// entries; class_method_* parses one method's signature + default).

#[partial]
def class_parser (input : String) : ParseResult Decl :=
	match vis_parser input {
		success rem vis => class_vis rem vis,
		fail e => fail e
	}

#[partial]
def class_vis (input : String) (vis : Visibility) : ParseResult Decl :=
	class_kw (tag "class" input) vis

#[partial]
def class_kw (r : ParseResult String) (vis : Visibility) : ParseResult Decl :=
	match r {
		success rem _ => class_constraints_or_name rem vis,
		fail e => fail e
	}

#[partial]
def class_constraints_or_name (input : String) (vis : Visibility) : ParseResult Decl :=
	class_try_constraints (tag "[" (skip_spaces input)) input vis

#[partial]
def class_try_constraints (r : ParseResult String) (orig : String) (vis : Visibility) : ParseResult Decl :=
	match r {
		success rem _ => class_constraints_bracket rem vis,
		fail _ => class_name (dotted_def_name (skip_spaces orig)) vis
	}

/// Parse the actual `[...]` constraint-list content (`type_constraint_list`,
/// same helper `instance`'s own constraint parsing already used) instead
/// of just `take_while`-skipping past it — the previous version consumed
/// the bracket's text but threw it away outright, so e.g. `class [BEq A]
/// Ord A { ... }` silently lost the `BEq A` constraint even though it
/// parsed "successfully". See `class_params`'s doc comment for how the
/// parsed constraints reach `Class.mk`.
#[partial]
def class_constraints_bracket (input : String) (vis : Visibility) : ParseResult Decl :=
	class_constraints_parsed (take_while is_not_bracket input) input vis

#[partial]
def class_constraints_parsed (r : ParseResult String) (orig : String) (vis : Visibility) : ParseResult Decl :=
	match r {
		success rem content =>
			class_constraints_then_name (type_constraint_list content) rem vis,
		fail _ => fail (ParseError.custom "expected ]" orig)
	}

#[partial]
def class_constraints_then_name (cr : ParseResult (List TypeConstraint)) (input : String) (vis : Visibility) : ParseResult Decl :=
	match cr {
		success _ constraints =>
			class_constraints_close_bracket (tag "]" input) constraints vis,
		fail _ =>
			let empty_cs : List TypeConstraint := List.empty in
			class_constraints_close_bracket (tag "]" input) empty_cs vis
	}

#[partial]
def class_constraints_close_bracket (r : ParseResult String) (constraints : List TypeConstraint) (vis : Visibility) : ParseResult Decl :=
	match r {
		success rem _ =>
			class_apply_constraints (class_name (dotted_def_name (skip_spaces rem)) vis) constraints,
		fail e => fail (ParseError.custom "expected ] after class constraint" (parse_error_remaining e))
	}

/// Patch the real constraints onto the fully-parsed `Class` — see
/// `class_params`'s doc comment for why this is done after the fact.
#[partial]
def class_apply_constraints (dr : ParseResult Decl) (constraints : List TypeConstraint) : ParseResult Decl :=
	match dr {
		success rem decl =>
			match decl {
				class_d cls =>
					match cls {
						Class.mk name params _ methods vis =>
							success rem (Decl.class_d (Class.mk name params constraints methods vis))
					},
				_ => success rem decl
			},
		fail e => fail e
	}

#[partial]
def class_name (r : ParseResult String) (vis : Visibility) : ParseResult Decl :=
	match r {
		success rem name =>
			let empty_params : List Param := List.empty in
			class_params rem (Identifier.id name) empty_params vis,
		fail e => fail e
	}

/// Class-level params, same shape as `type_params_loop` (which fixed this
/// exact bug for `type`/inductive params): bare identifiers (`class Map M
/// { ... }`) become implicit `Type`-kinded params, `(name : Type-expr)`
/// groups are parsed via `type_expression` — NOT the naive
/// `take_while is_not_close_paren` the previous version used, which broke
/// on any nested paren in the type (`class Map (M: (K : Type) -> (V :
/// Type) -> Type) { ... }`, `std/map.mo`'s very first decl, stopped at
/// the first `)` instead of the matching one). Both params AND
/// constraints are captured for real now — `class_close` still builds
/// the `Class` with placeholder empty lists, patched in afterward by
/// `class_apply_params`/`class_apply_constraints` once the whole
/// method-parsing subtree (which doesn't need either) has run, rather
/// than threading two more accumulators through all ~30 method-parsing
/// functions down to `class_close` (same "patch afterward" pattern
/// `instance_parser` already uses for `vis`/constraints/implicit params).
#[partial]
def class_params (input : String) (name : Identifier) (params : List Param) (vis : Visibility) : ParseResult Decl :=
	class_params_try_bare (identifier (skip_spaces input)) input name params vis

#[partial]
def class_params_try_bare (r : ParseResult String) (orig : String) (name : Identifier) (params : List Param) (vis : Visibility) : ParseResult Decl :=
	match r {
		success rem next =>
			class_params rem name (List.cons (param_many (Identifier.id next) (Term.type_ 1)) params) vis,
		fail _ => class_params_try_paren (tag "(" (skip_spaces orig)) orig name params vis
	}

#[partial]
def class_params_try_paren (r : ParseResult String) (orig : String) (name : Identifier) (params : List Param) (vis : Visibility) : ParseResult Decl :=
	match r {
		success rem _ => class_params_paren_name (identifier (skip_spaces rem)) name params vis,
		fail _ =>
			let rev : List Param := list_reverse params in
			class_apply_params (class_brace (tag "{" (skip_spaces orig)) name vis) rev
	}

#[partial]
def class_params_paren_name (r : ParseResult String) (name : Identifier) (params : List Param) (vis : Visibility) : ParseResult Decl :=
	match r {
		success rem pname => class_params_paren_colon (tag ":" (skip_spaces rem)) pname name params vis,
		fail e => fail e
	}

#[partial]
def class_params_paren_colon (r : ParseResult String) (pname : String) (name : Identifier) (params : List Param) (vis : Visibility) : ParseResult Decl :=
	match r {
		success rem _ =>
			let empty_ctx : List Identifier := List.empty in
			class_params_paren_type (type_expression empty_ctx rem) pname name params vis,
		fail e => fail e
	}

#[partial]
def class_params_paren_type (r : ParseResult Term) (pname : String) (name : Identifier) (params : List Param) (vis : Visibility) : ParseResult Decl :=
	match r {
		success rem typ => class_params_paren_default (tag ":=" (skip_spaces rem)) rem pname typ name params vis,
		fail e => fail e
	}

/// An optional `:= default` after a paren param's type — real usage:
/// `init/prelude.mo`'s `class FromListLiteral (L : Type -> Type := List)`.
/// Mirrors `struct_field_default`/`struct_field_default_val`'s shape.
#[partial]
def class_params_paren_default (r : ParseResult String) (orig : String) (pname : String) (typ : Term) (name : Identifier) (params : List Param) (vis : Visibility) : ParseResult Decl :=
	match r {
		success rem _ =>
			let empty_ctx : List Identifier := List.empty in
			class_params_paren_default_val (expression empty_ctx (skip_docstrings (skip_spaces rem))) pname typ name params vis,
		fail _ =>
			let none : Option Term := Option.none in
			class_params_paren_close (tag ")" (skip_spaces orig)) (Param.mk (Identifier.id pname) typ Multiplicity.many none List.empty) name params vis
	}

#[partial]
def class_params_paren_default_val (r : ParseResult Term) (pname : String) (typ : Term) (name : Identifier) (params : List Param) (vis : Visibility) : ParseResult Decl :=
	match r {
		success rem defval =>
			let some_val : Option Term := Option.some defval in
			class_params_paren_close (tag ")" (skip_spaces rem)) (Param.mk (Identifier.id pname) typ Multiplicity.many some_val List.empty) name params vis,
		fail e => fail e
	}

#[partial]
def class_params_paren_close (r : ParseResult String) (p : Param) (name : Identifier) (params : List Param) (vis : Visibility) : ParseResult Decl :=
	match r {
		success rem _ => class_params rem name (List.cons p params) vis,
		fail e => fail e
	}

/// Patch the real params onto the fully-parsed `Class` — see
/// `class_params`'s doc comment for why this is done after the fact
/// rather than threaded through the method-parsing subtree.
#[partial]
def class_apply_params (dr : ParseResult Decl) (params : List Param) : ParseResult Decl :=
	match dr {
		success rem decl =>
			match decl {
				class_d cls =>
					match cls {
						Class.mk name _ constraints methods vis =>
							success rem (Decl.class_d (Class.mk name params constraints methods vis))
					},
				_ => success rem decl
			},
		fail e => fail e
	}

#[partial]
def class_brace (r : ParseResult String) (name : Identifier) (vis : Visibility) : ParseResult Decl :=
	match r {
		success rem _ =>
			let empty_methods : List ClassDef := List.empty in
			class_methods rem name empty_methods vis,
		fail e => fail e
	}

#[partial]
def class_methods (input : String) (name : Identifier) (methods : List ClassDef) (vis : Visibility) : ParseResult Decl :=
	class_try_close_or_method (tag "def" (skip_docstrings (skip_spaces input))) (skip_docstrings (skip_spaces input)) name methods vis

#[partial]
def class_try_close_or_method (r : ParseResult String) (orig : String) (name : Identifier) (methods : List ClassDef) (vis : Visibility) : ParseResult Decl :=
	match r {
		success rem _ => class_methods_single rem name methods vis,
		fail _ => class_close (tag "}" (skip_spaces orig)) name methods vis
	}

#[partial]
def class_methods_single (input : String) (name : Identifier) (methods : List ClassDef) (vis : Visibility) : ParseResult Decl :=
	class_method_name (identifier (skip_spaces input)) name methods vis

#[partial]
def class_method_name (r : ParseResult String) (name : Identifier) (methods : List ClassDef) (vis : Visibility) : ParseResult Decl :=
	match r {
		success rem mname => class_method_colon_or_sig rem (Identifier.id mname) name methods vis,
		fail e => fail e
	}

#[partial]
def class_method_colon_or_sig (input : String) (mname : Identifier) (name : Identifier) (methods : List ClassDef) (vis : Visibility) : ParseResult Decl :=
	class_method_params_try (tag "(" (skip_spaces input)) input mname name methods List.empty vis

#[partial]
def class_method_params_try (r : ParseResult String) (orig : String) (mname : Identifier) (name : Identifier) (methods : List ClassDef) (param_types : List Term) (vis : Visibility) : ParseResult Decl :=
	match r {
		success rem _ => class_method_param_loop rem mname name methods param_types vis,
		fail _ => class_method_ret_type (tag ":" (skip_spaces orig)) mname name methods vis
	}

#[partial]
def class_method_param_loop (input : String) (mname : Identifier) (name : Identifier) (methods : List ClassDef) (param_types : List Term) (vis : Visibility) : ParseResult Decl :=
	class_method_one_param (identifier (skip_spaces input)) input mname name methods param_types vis

/// `group_start` is the position right after the group's `(`, before any
/// name has been consumed — kept around so that if this turns out to be
/// an unnamed/positional field (`(L A)`, e.g. `FromListLiteral.cons`'s
/// second param in init/prelude.mo) rather than `name(s) : Type`, the
/// whole group can be re-parsed from scratch as one bare type expression.
#[partial]
def class_method_one_param (r : ParseResult String) (orig : String) (mname : Identifier) (name : Identifier) (methods : List ClassDef) (param_types : List Term) (vis : Visibility) : ParseResult Decl :=
	match r {
		success rem pname => class_method_more_names rem mname name methods param_types 1 orig vis,
		fail _ => class_method_unnamed_param orig mname name methods param_types vis
	}

/// After the first name in a `(...)` param group, try to parse MORE
/// space-separated names sharing one type — supports `(a b : A)`, not
/// just `(a : A) (b : A)`.
#[partial]
def class_method_more_names (input : String) (mname : Identifier) (name : Identifier) (methods : List ClassDef) (param_types : List Term) (count : I64) (group_start : String) (vis : Visibility) : ParseResult Decl :=
	class_method_more_names_try (identifier (skip_spaces input)) input mname name methods param_types count group_start vis

#[partial]
def class_method_more_names_try (r : ParseResult String) (orig : String) (mname : Identifier) (name : Identifier) (methods : List ClassDef) (param_types : List Term) (count : I64) (group_start : String) (vis : Visibility) : ParseResult Decl :=
	match r {
		success rem pname => class_method_more_names rem mname name methods param_types (count + 1) group_start vis,
		fail _ => class_method_param_colon_or_unnamed (tag ":" (skip_spaces orig)) mname name methods param_types count group_start vis
	}

/// `orig`'s tokens parsed as one-or-more names, but no `:` follows —
/// re-parse from `group_start` as a single bare (unnamed/positional)
/// type instead, e.g. `(L A)` where "L" and "A" looked like two
/// space-separated names but are really an application `L A`.
#[partial]
def class_method_param_colon_or_unnamed (r : ParseResult String) (mname : Identifier) (name : Identifier) (methods : List ClassDef) (param_types : List Term) (count : I64) (group_start : String) (vis : Visibility) : ParseResult Decl :=
	match r {
		success rem _ =>
			let empty_ctx : List Identifier := List.empty in
			class_method_param_type (type_expression empty_ctx rem) mname name methods param_types count vis,
		fail _ => class_method_unnamed_param group_start mname name methods param_types vis
	}

/// Parse a group's content as a single bare/unnamed type (no `name :`
/// prefix at all), contributing exactly one param.
#[partial]
def class_method_unnamed_param (input : String) (mname : Identifier) (name : Identifier) (methods : List ClassDef) (param_types : List Term) (vis : Visibility) : ParseResult Decl :=
	let empty_ctx : List Identifier := List.empty in
	class_method_param_type (type_expression empty_ctx input) mname name methods param_types 1 vis

#[partial]
def class_method_param_colon (r : ParseResult String) (mname : Identifier) (name : Identifier) (methods : List ClassDef) (param_types : List Term) (count : I64) (vis : Visibility) : ParseResult Decl :=
	match r {
		success rem _ =>
			let empty_ctx : List Identifier := List.empty in
			class_method_param_type (type_expression empty_ctx rem) mname name methods param_types count vis,
		fail e => fail e
	}

#[partial]
def class_method_param_type (r : ParseResult Term) (mname : Identifier) (name : Identifier) (methods : List ClassDef) (param_types : List Term) (count : I64) (vis : Visibility) : ParseResult Decl :=
	match r {
		success rem typ => class_method_close_or_next rem mname name methods (push_n_terms typ count param_types) vis,
		fail e => fail e
	}

/// Cons `n` copies of `typ` onto `acc` — one per shared-type param name in
/// a `(a b c : Type)` group.
#[partial]
def push_n_terms (typ : Term) (n : I64) (acc : List Term) : List Term :=
	if I64.gt n 0 then push_n_terms typ (n - 1) (List.cons typ acc) else acc

#[partial]
def class_method_close_or_next (input : String) (mname : Identifier) (name : Identifier) (methods : List ClassDef) (param_types : List Term) (vis : Visibility) : ParseResult Decl :=
	class_method_try_close_param (tag ")" (skip_spaces input)) input mname name methods param_types vis

#[partial]
def class_method_try_close_param (r : ParseResult String) (orig : String) (mname : Identifier) (name : Identifier) (methods : List ClassDef) (param_types : List Term) (vis : Visibility) : ParseResult Decl :=
	match r {
		success rem _ => class_method_ret_or_more rem mname name methods param_types vis,
		fail _ => class_method_next_param (tag "(" (skip_spaces orig)) orig mname name methods param_types vis
	}

#[partial]
def class_method_ret_or_more (input : String) (mname : Identifier) (name : Identifier) (methods : List ClassDef) (param_types : List Term) (vis : Visibility) : ParseResult Decl :=
	class_method_try_ret_type (tag ":" (skip_spaces input)) input mname name methods param_types vis

#[partial]
def class_method_try_ret_type (r : ParseResult String) (orig : String) (mname : Identifier) (name : Identifier) (methods : List ClassDef) (param_types : List Term) (vis : Visibility) : ParseResult Decl :=
	match r {
		success rem _ =>
			let empty_ctx : List Identifier := List.empty in
			class_method_ret_type_val (type_expression empty_ctx rem) mname name methods param_types vis,
		fail _ => class_method_next_param (tag "(" (skip_spaces orig)) orig mname name methods param_types vis
	}

/// Combine every explicit param's type (parsed via `(...)` groups) with
/// the trailing return type into a real Pi chain `T1 -> T2 -> ... -> Ret`.
/// Previously the param types parsed inside `(...)` groups were parsed
/// then thrown away entirely (`class_method_param_type`'s old body
/// discarded its own `Term` via `success rem _ => ...`), and the method's
/// stored type was just the bare trailing return type — e.g.
/// `def map (f: A -> B) : (F A) -> F B` would store type `(F A) -> F B`,
/// silently dropping `(f: A -> B) ->` — a correctness bug independent of,
/// and worse than, the multi-name parsing failure this fix also covers.
#[partial]
def class_method_ret_type_val (r : ParseResult Term) (mname : Identifier) (name : Identifier) (methods : List ClassDef) (param_types : List Term) (vis : Visibility) : ParseResult Decl :=
	match r {
		success rem ret_typ => class_method_default_or_done rem mname (build_pi_chain param_types ret_typ) name methods vis,
		fail e => fail e
	}

/// Fold accumulated param types (most-recent-first / reverse declaration
/// order, same invariant `def`'s own `List Param` follows) with the
/// return type into a non-dependent Pi chain.
#[partial]
def build_pi_chain (param_types : List Term) (ret : Term) : Term := match param_types {
	List.empty => ret,
	List.cons t rest => build_pi_chain rest (Term.pi t ret),
}

#[partial]
def class_method_next_param (r : ParseResult String) (orig : String) (mname : Identifier) (name : Identifier) (methods : List ClassDef) (param_types : List Term) (vis : Visibility) : ParseResult Decl :=
	match r {
		success rem _ => class_method_param_loop rem mname name methods param_types vis,
		fail _ => fail (ParseError.custom "expected ) or another parameter" orig)
	}

#[partial]
def class_method_ret_type (r : ParseResult String) (mname : Identifier) (name : Identifier) (methods : List ClassDef) (vis : Visibility) : ParseResult Decl :=
	match r {
		success rem _ =>
			let empty_ctx : List Identifier := List.empty in
			class_method_sig_type (type_expression empty_ctx rem) mname name methods vis,
		fail e => fail (ParseError.custom "expected : return type" (parse_error_remaining e))
	}

#[partial]
def class_method_sig_type (r : ParseResult Term) (mname : Identifier) (name : Identifier) (methods : List ClassDef) (vis : Visibility) : ParseResult Decl :=
	match r {
		success rem typ => class_method_default_or_done rem mname typ name methods vis,
		fail e => fail e
	}

#[partial]
def class_method_default_or_done (input : String) (mname : Identifier) (typ : Term) (name : Identifier) (methods : List ClassDef) (vis : Visibility) : ParseResult Decl :=
	class_method_try_default (tag ":=" (skip_spaces input)) input mname typ name methods vis

#[partial]
def class_method_try_default (r : ParseResult String) (orig : String) (mname : Identifier) (typ : Term) (name : Identifier) (methods : List ClassDef) (vis : Visibility) : ParseResult Decl :=
	match r {
		success rem _ =>
			let empty_ctx : List Identifier := List.empty in
			class_method_default_val (expression empty_ctx (skip_docstrings (skip_spaces rem))) orig mname typ name methods vis,
		fail _ =>
			let none_val : Option Term := Option.none in
			class_methods orig name (List.cons (ClassDef.mk mname typ none_val) methods) vis
	}

#[partial]
def class_method_default_val (r : ParseResult Term) (orig : String) (mname : Identifier) (typ : Term) (name : Identifier) (methods : List ClassDef) (vis : Visibility) : ParseResult Decl :=
	match r {
		success rem defval =>
			let some_val : Option Term := Option.some defval in
			class_methods rem name (List.cons (ClassDef.mk mname typ some_val) methods) vis,
		fail e => fail e
	}

#[partial]
def class_close (r : ParseResult String) (name : Identifier) (methods : List ClassDef) (vis : Visibility) : ParseResult Decl :=
	match r {
		success rem _ =>
			let rev_methods : List ClassDef := list_reverse methods in
			let empty_params : List Param := List.empty in
			let empty_constraints : List TypeConstraint := List.empty in
			// Placeholders — class_apply_params/class_apply_constraints
			// patch the real values in afterward (see class_params's doc
			// comment; same pattern instance_close uses for vis).
			success rem (Decl.class_d (Class.mk name empty_params empty_constraints rev_methods vis)),
		fail e => fail e
	}

// instance [constraints] Class args { def method := body }
//
// Same shape as class_parser above: optional `[...]` constraints, the
// class name, zero-or-more argument terms (instance_args_or_brace loop),
// then a brace-delimited list of `def name (params) := body` method
// implementations (instance_methods loop; instance_method_* parses one
// method).

/// Unlike `class`, `vis` is patched onto the already-built `Instance`
/// afterward (mirroring `instance_set_constraints` just below, which does
/// the same for `[...]` constraints) rather than threaded through the
/// whole method-parsing recursion — `instance_close` itself doesn't need
/// to know the real value, sidestepping adding a parameter to every
/// function in `instance_methods`' loop.
#[partial]
def instance_parser (input : String) : ParseResult Decl :=
	match vis_parser input {
		success rem vis => instance_apply_vis (instance_kw (tag "instance" rem)) vis,
		fail e => fail e
	}

#[partial]
def instance_apply_vis (dr : ParseResult Decl) (vis : Visibility) : ParseResult Decl :=
	match dr {
		success rem decl =>
			match decl {
				instance_d inst =>
					match inst {
						Instance.mk name cls constraints args _ implicit_params =>
							success rem (Decl.instance_d (Instance.mk name cls constraints args vis implicit_params))
					},
				_ => success rem decl
			},
		fail e => fail e
	}

#[partial]
def instance_kw (r : ParseResult String) : ParseResult Decl :=
	match r {
		success rem _ =>
			let empty : List Param := List.empty in
			instance_implicit_params_loop (skip_spaces rem) empty,
		fail e => fail e
	}

/// Parse zero or more `{name : Type}` implicit-binder clauses right after
/// the `instance` keyword (e.g. `instance {A : Type} Show A { ... }`),
/// mirroring the Rust reference's `implicit_params` (`fold_many0` over
/// `implicit_param`). Unlike `def`'s implicit params (`def_implicit_param`,
/// which deliberately discards its clause's content since `elaborate_def`
/// auto-generalizes free type vars anyway), these ARE captured for real:
/// `Instance.implicit_params` is load-bearing for instance resolution on
/// the Rust side (substitution-based matching against a lookup key's
/// args — see `Instance.params` in core/src/term.rs), so there's no
/// auto-generalization step to fall back on here.
#[partial]
def instance_implicit_params_loop (input : String) (params : List Param) : ParseResult Decl :=
	instance_implicit_try (tag "{" input) input params

#[partial]
def instance_implicit_try (r : ParseResult String) (orig : String) (params : List Param) : ParseResult Decl :=
	match r {
		success rem _ => instance_implicit_param (identifier (skip_spaces rem)) rem params,
		fail _ =>
			let rev : List Param := list_reverse params in
			instance_apply_params (instance_try_constraints (tag "[" (skip_spaces orig)) orig) rev
	}

#[partial]
def instance_implicit_param (r : ParseResult String) (brace_rem : String) (params : List Param) : ParseResult Decl :=
	match r {
		success rem2 name => instance_implicit_more_names rem2 brace_rem (List.cons (Identifier.id name) List.empty) params,
		fail e => fail e
	}

/// After the first name in a `{...}` clause, try more space-separated
/// names sharing one type (`{K V : Type}`), same shape as
/// `def_explicit_more_names`.
#[partial]
def instance_implicit_more_names (input : String) (brace_rem : String) (names : List Identifier) (params : List Param) : ParseResult Decl :=
	instance_implicit_more_names_try (identifier (skip_spaces input)) input brace_rem names params

#[partial]
def instance_implicit_more_names_try (r : ParseResult String) (orig : String) (brace_rem : String) (names : List Identifier) (params : List Param) : ParseResult Decl :=
	match r {
		success rem2 name => instance_implicit_more_names rem2 brace_rem (List.cons (Identifier.id name) names) params,
		fail _ => instance_implicit_colon (tag ":" (skip_spaces orig)) names params
	}

#[partial]
def instance_implicit_colon (r : ParseResult String) (names : List Identifier) (params : List Param) : ParseResult Decl :=
	match r {
		success rem2 _ =>
			let empty_ctx : List Identifier := List.empty in
			instance_implicit_type (type_expression empty_ctx rem2) names params,
		fail e => fail e
	}

#[partial]
def instance_implicit_type (r : ParseResult Term) (names : List Identifier) (params : List Param) : ParseResult Decl :=
	match r {
		success rem2 typ => instance_implicit_close (tag "}" rem2) names typ params,
		fail e => fail e
	}

/// Closes a `{name : type}` clause and loops back for another one (the
/// Rust reference's `fold_many0`) — unlike `def_implicit_close`, this
/// keeps what it parsed: builds one real `Param` per name via the shared
/// `params_for_names` helper and folds it into the accumulator before
/// retrying.
#[partial]
def instance_implicit_close (r : ParseResult String) (names : List Identifier) (typ : Term) (params : List Param) : ParseResult Decl :=
	match r {
		success rem2 _ =>
			instance_implicit_params_loop (skip_spaces rem2) (params_for_names (list_reverse names) typ params),
		fail e => fail e
	}

/// Patch the collected implicit params onto the fully-parsed `Instance`,
/// same "parse with a placeholder, patch the real value in afterward"
/// pattern already used for `vis` (`instance_apply_vis`) and constraints
/// (`instance_set_constraints`) — cheaper than threading `params` through
/// every function from here down to `instance_close`.
#[partial]
def instance_apply_params (dr : ParseResult Decl) (params : List Param) : ParseResult Decl :=
	match dr {
		success rem decl =>
			match decl {
				instance_d inst =>
					match inst {
						Instance.mk name cls constraints args vis _ =>
							success rem (Decl.instance_d (Instance.mk name cls constraints args vis params))
					},
				_ => success rem decl
			},
		fail e => fail e
	}

#[partial]
def instance_try_constraints (r : ParseResult String) (orig : String) : ParseResult Decl :=
	match r {
		success rem _ => instance_parse_bracket rem,
		fail _ => instance_name (module_path_parser (skip_spaces orig))
	}

#[partial]
def instance_parse_bracket (input : String) : ParseResult Decl :=
	instance_constraints_with_bracket (take_while is_not_bracket input) input

#[partial]
def instance_constraints_with_bracket (r : ParseResult String) (orig : String) : ParseResult Decl :=
	match r {
		success rem content =>
			instance_constraints_then_name (type_constraint_list content) rem,
		fail _ => fail (ParseError.custom "expected ]" orig)
	}

#[partial]
def instance_constraints_then_name (cr : ParseResult (List TypeConstraint)) (input : String) : ParseResult Decl :=
	match cr {
		success _ constraints =>
			instance_constraints_close_bracket (tag "]" input) constraints,
		fail _ =>
			let empty_cs : List TypeConstraint := List.empty in
			instance_constraints_close_bracket (tag "]" input) empty_cs
	}

#[partial]
def instance_constraints_close_bracket (r : ParseResult String) (constraints : List TypeConstraint) : ParseResult Decl :=
	match r {
		success rem _ =>
			instance_set_constraints (instance_name (module_path_parser (skip_spaces rem))) constraints,
		fail e => fail (ParseError.custom "expected ] after instance constraint" (parse_error_remaining e))
	}

#[partial]
def instance_set_constraints (dr : ParseResult Decl) (constraints : List TypeConstraint) : ParseResult Decl :=
	match dr {
		success rem decl =>
			match decl {
				instance_d inst =>
					match inst {
						Instance.mk name cls _ args vis implicit_params =>
							success rem (Decl.instance_d (Instance.mk name cls constraints args vis implicit_params))
					},
				_ => success rem decl
			},
		fail e => fail e
	}

#[partial]
def instance_name (r : ParseResult ModulePath) : ParseResult Decl :=
	match r {
		success rem path =>
			let empty_args : List Term := List.empty in
			instance_args_or_brace rem path empty_args,
		fail e => fail e
	}

#[partial]
def instance_args_or_brace (input : String) (cls : ModulePath) (args : List Term) : ParseResult Decl :=
	let empty_ctx : List Identifier := List.empty in
	instance_try_arg (atom_term empty_ctx (skip_spaces input)) input cls args

#[partial]
def instance_try_arg (r : ParseResult Term) (orig : String) (cls : ModulePath) (args : List Term) : ParseResult Decl :=
	match r {
		success rem arg => instance_args_or_brace rem cls (List.cons arg args),
		fail _ => instance_brace (tag "{" (skip_spaces orig)) cls args
	}

#[partial]
def instance_brace (r : ParseResult String) (cls : ModulePath) (args : List Term) : ParseResult Decl :=
	match r {
		success rem _ =>
			let empty_methods : List Def := List.empty in
			instance_methods rem cls args empty_methods,
		fail e => fail e
	}

#[partial]
def instance_methods (input : String) (cls : ModulePath) (args : List Term) (methods : List Def) : ParseResult Decl :=
	let cleaned : String := skip_one_attr (skip_docstrings (skip_spaces input)) in
	instance_try_close_or_def (tag "def" cleaned) cleaned cls args methods

#[partial]
def instance_try_close_or_def (r : ParseResult String) (orig : String) (cls : ModulePath) (args : List Term) (methods : List Def) : ParseResult Decl :=
	match r {
		success rem _ => instance_method_single rem cls args methods,
		fail _ => instance_close (tag "}" (skip_spaces orig)) cls args methods
	}

// Instance methods use a real, typed `def`-shaped signature in every real
// example in the corpus (`def beq (a b : Bool) : Bool := ...`), matching
// top-level `def` syntax exactly (implicit `{...}` params, explicit
// `(...)` params incl. multi-name groups, a `:` return type, then a body)
// — NOT bare untyped patterns. The previous implementation tried to parse
// each param as a pattern-style `atom_term` (no `:` support at all, so
// any typed param immediately failed) and always stored `Term.hole` as
// the method's type even when it did parse something. This reuses
// `def_params_loop` (the same parser `def` itself uses, so multi-name
// groups and implicit params work identically) and builds a real Pi-typed
// signature via `build_param_pi_chain`, with the body correctly wrapped
// in one lambda per param via the existing `lam_params`.
#[partial]
def instance_method_single (input : String) (cls : ModulePath) (args : List Term) (methods : List Def) : ParseResult Decl :=
	instance_method_name (dotted_def_name (skip_spaces input)) cls args methods

#[partial]
def instance_method_name (r : ParseResult String) (cls : ModulePath) (args : List Term) (methods : List Def) : ParseResult Decl :=
	match r {
		success rem name => instance_method_params rem (Identifier.id name) cls args methods,
		fail e => fail e
	}

#[partial]
def instance_method_params (input : String) (name : Identifier) (cls : ModulePath) (args : List Term) (methods : List Def) : ParseResult Decl :=
	instance_method_params_done (def_params_loop (skip_spaces input) List.empty) name cls args methods

#[partial]
def instance_method_params_done (r : ParseResult (List Param)) (name : Identifier) (cls : ModulePath) (args : List Term) (methods : List Def) : ParseResult Decl :=
	match r {
		success rem params => instance_method_ret_type (tag ":" (skip_spaces rem)) rem name params cls args methods,
		fail e => fail e
	}

/// The dominant real-corpus shape is a full `def`-style typed signature
/// (`def beq (a b : Bool) : Bool := ...`), handled by `def_params_loop`
/// above and the Pi-chain construction below. But an older, untyped
/// bare-pattern-args shape (`def show xs := "list"`, no parens, no `:`)
/// is also real, still-tested syntax — `def_params_loop` only recognizes
/// `{...}`/`(...)` groups, so on bare `xs := ...` it matches neither and
/// returns immediately with zero params and `rem` unmoved, landing here
/// with no `:` to find. Fall back to the untyped pattern-args loop in
/// that case instead of hard-failing.
#[partial]
def instance_method_ret_type (r : ParseResult String) (orig : String) (name : Identifier) (params : List Param) (cls : ModulePath) (args : List Term) (methods : List Def) : ParseResult Decl :=
	match r {
		// `tag ":"` also matches the leading character of `:=` (the
		// zero-arg untyped shape, `def m := a`) — check for that exact
		// case first so it doesn't get misread as "found a `:` return
		// type" and then fail trying to parse a type starting at `= a`.
		success rem _ => instance_method_ret_type_not_assign (tag "=" rem) orig rem name params cls args methods,
		fail _ => instance_method_untyped_args_loop orig List.empty name cls args methods
	}

#[partial]
def instance_method_ret_type_not_assign (r : ParseResult String) (orig : String) (after_colon : String) (name : Identifier) (params : List Param) (cls : ModulePath) (args : List Term) (methods : List Def) : ParseResult Decl :=
	match r {
		success rem _ => instance_method_untyped_args_loop orig List.empty name cls args methods,
		fail _ =>
			let empty_ctx : List Identifier := List.empty in
			instance_method_ret_expr (type_expression empty_ctx after_colon) name params cls args methods
	}

/// Untyped fallback: bare pattern-style args (`f m := ...`, possibly
/// zero), matching the pre-existing (if semantically incomplete — the
/// parsed args were never bound as lambdas over the body even before
/// this fix, only ever checked for successful parsing, never evaluated)
/// behavior for this shape.
#[partial]
def instance_method_untyped_args_loop (input : String) (body_args : List Term) (name : Identifier) (cls : ModulePath) (args : List Term) (methods : List Def) : ParseResult Decl :=
	let empty_ctx : List Identifier := List.empty in
	instance_method_untyped_args_next (atom_term empty_ctx (skip_spaces input)) input body_args name cls args methods

#[partial]
def instance_method_untyped_args_next (r : ParseResult Term) (orig : String) (body_args : List Term) (name : Identifier) (cls : ModulePath) (args : List Term) (methods : List Def) : ParseResult Decl :=
	match r {
		success rem arg => instance_method_untyped_args_loop rem (List.cons arg body_args) name cls args methods,
		fail _ => instance_method_untyped_finish (tag ":=" (skip_spaces orig)) name cls args methods
	}

#[partial]
def instance_method_untyped_finish (r : ParseResult String) (name : Identifier) (cls : ModulePath) (args : List Term) (methods : List Def) : ParseResult Decl :=
	match r {
		success rem _ =>
			let empty_ctx : List Identifier := List.empty in
			instance_method_untyped_body (expression empty_ctx (skip_docstrings (skip_spaces rem))) name cls args methods,
		fail e => fail (ParseError.custom "expected := in instance method" (parse_error_remaining e))
	}

#[partial]
def instance_method_untyped_body (r : ParseResult Term) (name : Identifier) (cls : ModulePath) (args : List Term) (methods : List Def) : ParseResult Decl :=
	match r {
		success rem body =>
			let empty_constraints : List TypeConstraint := List.empty in
			let empty_attrs : List Attribute := List.empty in
			let d : Def := Def.mk (ModulePath.mp (List.cons name List.empty)) (Term.hole) body empty_constraints empty_attrs Visibility.package_private in
			instance_methods rem cls args (List.cons d methods),
		fail e => fail e
	}

#[partial]
def instance_method_ret_expr (r : ParseResult Term) (name : Identifier) (params : List Param) (cls : ModulePath) (args : List Term) (methods : List Def) : ParseResult Decl :=
	match r {
		success rem ret_typ => instance_method_body_start rem name params ret_typ cls args methods,
		fail e => fail e
	}

#[partial]
def instance_method_body_start (input : String) (name : Identifier) (params : List Param) (ret_typ : Term) (cls : ModulePath) (args : List Term) (methods : List Def) : ParseResult Decl :=
	instance_method_body_assign (tag ":=" (skip_spaces input)) name params ret_typ cls args methods

#[partial]
def instance_method_body_assign (r : ParseResult String) (name : Identifier) (params : List Param) (ret_typ : Term) (cls : ModulePath) (args : List Term) (methods : List Def) : ParseResult Decl :=
	match r {
		success rem _ => instance_method_body_block_or_expr rem name params ret_typ cls args methods,
		fail e => fail (ParseError.custom "expected := in instance method" (parse_error_remaining e))
	}

/// Body is either a `do { ... }` block or a bare expression — mirrors
/// `def`'s own `def_body_block_or_none`/`def_body_do` alternative.
#[partial]
def instance_method_body_block_or_expr (input : String) (name : Identifier) (params : List Param) (ret_typ : Term) (cls : ModulePath) (args : List Term) (methods : List Def) : ParseResult Decl :=
	instance_method_try_block (tag "{" (skip_spaces input)) input name params ret_typ cls args methods

#[partial]
def instance_method_try_block (r : ParseResult String) (orig : String) (name : Identifier) (params : List Param) (ret_typ : Term) (cls : ModulePath) (args : List Term) (methods : List Def) : ParseResult Decl :=
	match r {
		success rem _ => instance_method_body_do (do_stmts (ctx_of_params params) rem) name params ret_typ cls args methods,
		fail _ =>
			let empty_ctx : List Identifier := List.empty in
			instance_method_body_expr (expression (ctx_of_params params) (skip_docstrings (skip_spaces orig))) name params ret_typ cls args methods
	}

#[partial]
def instance_method_body_do (r : ParseResult (List DoStmt)) (name : Identifier) (params : List Param) (ret_typ : Term) (cls : ModulePath) (args : List Term) (methods : List Def) : ParseResult Decl :=
	match r {
		success rem stmts => instance_method_finish rem name params ret_typ (desugar_do stmts) cls args methods,
		fail e => fail e
	}

#[partial]
def instance_method_body_expr (r : ParseResult Term) (name : Identifier) (params : List Param) (ret_typ : Term) (cls : ModulePath) (args : List Term) (methods : List Def) : ParseResult Decl :=
	match r {
		success rem body => instance_method_finish rem name params ret_typ body cls args methods,
		fail e => fail e
	}

#[partial]
def instance_method_finish (input : String) (name : Identifier) (params : List Param) (ret_typ : Term) (body : Term) (cls : ModulePath) (args : List Term) (methods : List Def) : ParseResult Decl :=
	let empty_constraints : List TypeConstraint := List.empty in
	let empty_attrs : List Attribute := List.empty in
	let full_typ := build_param_pi_chain params ret_typ in
	let d : Def := Def.mk (ModulePath.mp (List.cons name List.empty)) full_typ (lam_params params body) empty_constraints empty_attrs Visibility.package_private in
	instance_methods input cls args (List.cons d methods)

/// Fold a `List Param` (already in left-to-right declaration order — the
/// `def_params_loop` result, same as `def` itself consumes) into a Pi
/// chain with the return type.
#[partial]
def build_param_pi_chain (params : List Param) (ret : Term) : Term := match params {
	List.empty => ret,
	List.cons p rest =>
		match p {
			Param.mk pname typ mult default _attrs => Term.pi typ (build_param_pi_chain rest ret)
		},
}

#[partial]
def instance_close (r : ParseResult String) (cls : ModulePath) (args : List Term) (methods : List Def) : ParseResult Decl :=
	match r {
		success rem _ =>
			let rev_methods : List Def := list_reverse methods in
			let rev_args : List Term := list_reverse args in
			let empty_constraints : List TypeConstraint := List.empty in
			let empty_params : List Param := List.empty in
			// Placeholder — instance_parser's instance_apply_vis and
			// instance_apply_params patch the real values in afterward.
			success rem (Decl.instance_d (Instance.mk (Identifier.id "_") cls empty_constraints rev_args Visibility.package_private empty_params)),
		fail e => fail e
	}

// ─── `defmacro` (both forms) ─────────────────────────────────────────────
//
// `defmacro name params := <term>` (Decl.def_macro_d) and `defmacro name
// params := decls { ... }` (Decl.decl_gen_d) share an identical prefix
// (`"defmacro" name params :=`) — parsed ONCE here (unlike the Rust
// reference's own fully-backtracking `alt(decl_gen_parser,
// defmacro_parser)`, which reparses the shared prefix twice), then a
// single dispatch point tries `decls {` first, falling back to a plain
// term. Matches this file's own existing "try A, fall back to B" idiom
// (`def_try_constraints`, above). Parsing/representation only — see
// `Decl.def_macro_d`/`decl_gen_d`'s own doc comments in lang/types.mo.

/// One macro parameter: a bare identifier (untyped, `typ = Term.hole`)
/// or a parenthesized `(x : T)` group (optional multiplicity prefix).
/// Mirrors the reference's own `macro_param` (core/src/parser.rs) --
/// reuses the same building blocks `def`'s own explicit-param chain
/// does (`multiplicity_prefix`), just without the `{implicit}`
/// alternative (defmacro has no implicit-param syntax) and without
/// multi-name-sharing-one-type support (`(x y : T)`) -- confirmed via
/// the corpus's own 4 real `defmacro`s (std/derive.mo) that every one
/// uses a single bare-identifier param; multi-name support here would
/// be unverified complexity with nothing to test it against.
#[partial]
def macro_param (input : String) : ParseResult Param :=
	macro_param_try_paren (tag "(" input) input

#[partial]
def macro_param_try_paren (r : ParseResult String) (orig : String) : ParseResult Param :=
	match r {
		success rem _ => macro_param_paren_mult (multiplicity_prefix rem) rem,
		fail _ => macro_param_try_bare orig
	}

#[partial]
def macro_param_try_bare (input : String) : ParseResult Param :=
	match identifier input {
		success rem name => success rem (param_many (Identifier.id name) Term.hole),
		fail e => fail e
	}

#[partial]
def macro_param_paren_mult (r : ParseResult Multiplicity) (orig : String) : ParseResult Param :=
	match r {
		success rem mult => macro_param_paren_name (identifier (skip_spaces rem)) mult,
		fail e => fail e
	}

#[partial]
def macro_param_paren_name (r : ParseResult String) (mult : Multiplicity) : ParseResult Param :=
	match r {
		success rem name => macro_param_paren_colon (tag ":" (skip_spaces rem)) (Identifier.id name) mult,
		fail e => fail e
	}

#[partial]
def macro_param_paren_colon (r : ParseResult String) (name : Identifier) (mult : Multiplicity) : ParseResult Param :=
	match r {
		success rem _ =>
			let empty_ctx : List Identifier := List.empty in
			macro_param_paren_type (type_expression empty_ctx (skip_spaces rem)) name mult,
		fail e => fail e
	}

#[partial]
def macro_param_paren_type (r : ParseResult Term) (name : Identifier) (mult : Multiplicity) : ParseResult Param :=
	match r {
		success rem typ => macro_param_paren_close (tag ")" (skip_spaces rem)) name typ mult,
		fail e => fail e
	}

#[partial]
def macro_param_paren_close (r : ParseResult String) (name : Identifier) (typ : Term) (mult : Multiplicity) : ParseResult Param :=
	match r {
		success rem _ =>
			let none : Option Term := Option.none in
			let no_attrs : List Attribute := List.empty in
			success rem (Param.mk name typ mult none no_attrs),
		fail e => fail e
	}

#[partial]
def macro_params (input : String) : ParseResult (List Param) :=
	macro_params_loop (skip_spaces input) List.empty

#[partial]
def macro_params_loop (input : String) (acc : List Param) : ParseResult (List Param) :=
	match macro_param input {
		success rem p => macro_params_loop (skip_spaces rem) (List.cons p acc),
		fail _ => success input (list_reverse acc)
	}

#[partial]
def defmacro_parser (input : String) : ParseResult Decl :=
	defmacro_kw (tag "defmacro" input)

#[partial]
def defmacro_kw (r : ParseResult String) : ParseResult Decl :=
	match r {
		success rem _ => defmacro_ws1 (ws1 rem),
		fail e => fail e
	}

#[partial]
def defmacro_ws1 (r : ParseResult String) : ParseResult Decl :=
	match r {
		success rem _ => defmacro_name (dotted_def_name (skip_spaces rem)),
		fail e => fail e
	}

#[partial]
def defmacro_name (r : ParseResult String) : ParseResult Decl :=
	match r {
		success rem name => defmacro_params_result (macro_params rem) (Identifier.id name),
		fail e => fail e
	}

#[partial]
def defmacro_params_result (r : ParseResult (List Param)) (name : Identifier) : ParseResult Decl :=
	match r {
		success rem params => defmacro_assign (tag ":=" (skip_spaces rem)) name params,
		fail e => fail e
	}

#[partial]
def defmacro_assign (r : ParseResult String) (name : Identifier) (params : List Param) : ParseResult Decl :=
	match r {
		success rem _ =>
			let after_assign : String := skip_spaces rem in
			defmacro_try_decls_block (tag "decls" after_assign) after_assign name params,
		fail e => fail e
	}

#[partial]
def defmacro_try_decls_block (r : ParseResult String) (orig : String) (name : Identifier) (params : List Param) : ParseResult Decl :=
	match r {
		success rem _ => defmacro_decls_open (tag "{" (skip_spaces rem)) name params,
		fail _ => defmacro_term_body (type_expression (ctx_of_params params) (skip_docstrings (skip_spaces orig))) name params
	}

#[partial]
def defmacro_term_body (r : ParseResult Term) (name : Identifier) (params : List Param) : ParseResult Decl :=
	match r {
		success rem term =>
			let body : Term := lam_params params term in
			let mp : ModulePath := ModulePath.mp (List.cons name List.empty) in
			let no_attrs : List Attribute := List.empty in
			let no_constraints : List TypeConstraint := List.empty in
			success rem (Decl.def_macro_d (Def.mk mp Term.hole body no_constraints no_attrs Visibility.package_private)),
		fail e => fail e
	}

/// `decls { ... }` (Form A's body) reuses the EXISTING `decls_skip`
/// truncate-on-fail loop directly — the same one `decls_parser` (the
/// module-level decl-list parser) already uses. Confirmed structurally
/// identical to the reference's own `decls_until_end` (a hand-rolled
/// loop, not nom combinators there either), and confirmed the
/// reference's `decl_parser_no_macro`/`decl_parser` are byte-for-byte
/// the same alternation (both allow NESTED `defmacro`/macro-call decl_list
/// — needed since `std/derive.mo`'s own macros call `reflect_type_info!
/// T ...meta` inside their own `decl_list{}` bodies) — so reusing this
/// file's single, unified `decl_parser`/`decls_skip` here (rather than
/// inventing a separate "no-macro" variant) matches the reference
/// exactly, and needs no new termination-guarding machinery.
#[partial]
def defmacro_decls_open (r : ParseResult String) (name : Identifier) (params : List Param) : ParseResult Decl :=
	match r {
		success rem _ => defmacro_decls_result (decls_skip (skip_spaces rem) List.empty) name params,
		fail e => fail e
	}

#[partial]
def defmacro_decls_result (r : ParseResult (List Decl)) (name : Identifier) (params : List Param) : ParseResult Decl :=
	match r {
		success rem decl_list => defmacro_decls_close (tag "}" (skip_spaces rem)) name params decl_list,
		fail e => fail e
	}

#[partial]
def defmacro_decls_close (r : ParseResult String) (name : Identifier) (params : List Param) (decl_list : List Decl) : ParseResult Decl :=
	match r {
		success rem _ =>
			let mp : ModulePath := ModulePath.mp (List.cons name List.empty) in
			let no_attrs : List Attribute := List.empty in
			success rem (Decl.decl_gen_d mp params decl_list no_attrs),
		fail e => fail (ParseError.custom "expected } to close decl_list block" "")
	}

// ─── Declaration-position `name! args...` ───────────────────────────────
//
// Mirrors the reference's `macro_call_decl_parser`/`macro_call_decl_arg`
// (core/src/parser.rs). Args are whitespace-separated terms (not a
// comma/paren-delimited call) parsed via a RESTRICTED atom set that
// deliberately excludes `macro_call_term`/general application, guarded
// by a lookahead so a second decl-level macro call on the next line
// doesn't get swallowed as an extra argument of the first — real
// corpus shape: `std/derive.mo`'s `reflect_type_info! T
// derive_lens_meta` (two bare-identifier args).

#[partial]
def macro_call_decl_arg (input : String) : ParseResult Term :=
	macro_call_decl_arg_guard (peek_not_macro_call input) input

#[partial]
def macro_call_decl_arg_guard (r : ParseResult String) (input : String) : ParseResult Term :=
	match r {
		success _ _ => macro_call_decl_arg_alt input,
		fail e => fail e
	}

/// `peek(not(pair(identifier, tag "!")))` — succeeds (consuming
/// nothing) unless `input` starts with `<identifier>!`, in which case
/// it fails, causing `macro_call_decl_arg` as a whole to fail (never
/// swallowing another macro call as an argument).
#[partial]
def peek_not_macro_call (input : String) : ParseResult String :=
	match identifier input {
		success rem _ =>
			match tag "!" rem {
				success _ _ => fail (ParseError.custom "unexpected macro call in argument position" input),
				fail _ => success input ""
			},
		fail _ => success input ""
	}

#[partial]
def macro_call_decl_arg_alt (input : String) : ParseResult Term :=
	alt_fold [quote_term_parser List.empty, do_parser List.empty, let_term_parser List.empty,
	          if_parser List.empty, match_parser List.empty, variable List.empty,
	          literal_parser, lambda_parser List.empty, paren_expr List.empty] input

#[partial]
def macro_call_decl_parser (input : String) : ParseResult Decl :=
	macro_call_decl_guard (peek_not_macro_call input) input

#[partial]
def macro_call_decl_guard (r : ParseResult String) (input : String) : ParseResult Decl :=
	match r {
		// `peek_not_macro_call` succeeding here (no `!`) means this ISN'T
		// a macro call at all -- correctly fail so `decl_parsers`' other
		// alternatives get a chance instead of misreporting "unexpected
		// macro call" for completely ordinary input.
		success _ _ => fail (ParseError.custom "not a macro call" input),
		fail _ => macro_call_decl_name (identifier input) input
	}

#[partial]
def macro_call_decl_name (r : ParseResult String) (orig : String) : ParseResult Decl :=
	match r {
		success rem name => macro_call_decl_bang (tag "!" rem) (Identifier.id name),
		fail e => fail e
	}

#[partial]
def macro_call_decl_bang (r : ParseResult String) (name : Identifier) : ParseResult Decl :=
	match r {
		success rem _ => macro_call_decl_args (skip_spaces rem) name List.empty,
		fail e => fail e
	}

#[partial]
def macro_call_decl_args (input : String) (name : Identifier) (acc : List Term) : ParseResult Decl :=
	match macro_call_decl_arg input {
		success rem t => macro_call_decl_args (skip_spaces rem) name (List.cons t acc),
		fail _ => success input (Decl.macro_call_d name (list_reverse acc))
	}

// Canonical decl dispatcher

// `#[partial]` needed now that `decl_parsers` is part of a genuine
// mutual-recursion cycle (decl_parsers -> defmacro_parser ->
// defmacro_decls_open -> decls_skip -> decl_parser -> decl_parsers,
// for a nested `decls { ... }` block) -- same reason `atom_parsers`
// above already carries it (that one cycles through the whole
// expression grammar the same way).
#[partial]
def decl_parsers : List (String -> ParseResult Decl) :=
	[use_parser, open_parser, infix_parser, defmacro_parser, def_parser,
	 struct_parser, type_parser, class_parser, instance_parser, macro_call_decl_parser]

#[partial]
def decl_parser (input : String) : ParseResult Decl :=
	decl_fail_to_unknown (alt_fold decl_parsers input) input

/// Now that `alt_fold` tracks furthest-progress-wins across
/// `decl_parsers`'s alternatives (see `lang/parser/combinators.mo`'s
/// `furthest_error`), a failure that got partway into a real construct
/// (e.g. matched the `def` keyword, then failed inside its parameter
/// list) already carries a specific, correctly-positioned message —
/// relabeling it to "unknown declaration" would throw that away. Only
/// fall back to the generic message when NONE of `decl_parsers` got
/// any further than `decl_parser`'s own starting position (i.e. the
/// input didn't match the start of any known declaration form at all).
#[partial]
def decl_fail_to_unknown (r : ParseResult Decl) (input : String) : ParseResult Decl :=
	match r {
		success rem out => success rem out,
		fail e =>
			if I64.beq (String.length (parse_error_remaining e)) (String.length input)
			then fail (ParseError.custom "unknown declaration" (parse_error_remaining e))
			else fail e
	}

// ─── Multiple declaration parser (file-level) ──────────────────────────

#[partial]
def decls_parser (input : String) : ParseResult (List Decl) :=
	decls_skip (skip_docstrings (skip_spaces input)) List.empty

#[partial]
def decls_skip (input : String) (acc : List Decl) : ParseResult (List Decl) :=
	decls_try (decl_parser input) input acc

#[partial]
def decls_try (r : ParseResult Decl) (orig : String) (acc : List Decl) : ParseResult (List Decl) :=
	match r {
		success rem decl => decls_skip (skip_docstrings (skip_spaces rem)) (List.cons decl acc),
		// KNOWN GAP: on a real parse failure with content still remaining
		// (not true end-of-file), this silently stops and reports success
		// with whatever was accumulated so far — every declaration from
		// here to EOF is discarded with no diagnostic. A line-by-line
		// resync-and-continue fix was tried and reached much further into
		// real files, but it can misparse an orphaned inner line of a
		// broken multi-line construct (e.g. a class method whose own
		// signature also happens to be valid as a standalone top-level
		// def) as a spurious extra declaration — confirmed to regress
		// `slow_tests/typecheck_init_tests.mo` /
		// `slow_tests/typecheck_std_tests.mo` (12 tests). Reverted until
		// resync can be scoped to not leak decl_list from inside a construct
		// that failed as a whole (e.g. only resync at genuine top-level
		// keyword boundaries AND validate recovered decl_list don't reference
		// names that were never in scope at the top level).
		fail _ => success orig (list_reverse acc)
	}

/// A `decls_parser` twin that actually propagates a real failure instead
/// of silently truncating (`decls_try`'s own doc comment above explains
/// why the lenient version can't just be flipped to strict in place: a
/// resync-and-continue attempt at making truncation itself smarter
/// regressed 12 typecheck tests by leaking a misparsed inner line as a
/// spurious top-level decl). This is a SEPARATE function, not a
/// replacement, specifically so nothing that already depends on the
/// lenient behavior (`lang.module`'s scope-building, and by extension
/// most of this corpus's own test suite) breaks. `lang/json.mo`/
/// `lang/toml.mo`/`std/map.mo` were the real files motivating this split
/// in the first place — confirmed (2026-08-19) to now fully self-parse
/// with `decls_parser` too (see `slow_tests/parser_file_tests.mo`'s
/// `test_json_fully_parses`/`test_toml_fully_parses`/
/// `test_map_fully_parses`), but the strict twin stays regardless since
/// the lenient parser can still silently truncate on OTHER not-yet-
/// encountered constructs, and a real diagnostic on failure is worth
/// having independent of any specific file's current status. Used only
/// where a real diagnostic is actually wanted: `lang.module`'s
/// `try_parse_decls_strict`, wired into `lang/main.mo`'s CLI
/// compile-failure path.
#[partial]
def decls_parser_strict (input : String) : ParseResult (List Decl) :=
	decls_skip_strict (skip_docstrings (skip_spaces input)) List.empty

#[partial]
def decls_skip_strict (input : String) (acc : List Decl) : ParseResult (List Decl) :=
	if is_empty input
	then success input (list_reverse acc)
	else decls_try_strict (decl_parser input) acc

#[partial]
def decls_try_strict (r : ParseResult Decl) (acc : List Decl) : ParseResult (List Decl) :=
	match r {
		success rem decl => decls_skip_strict (skip_docstrings (skip_spaces rem)) (List.cons decl acc),
		fail e => fail e
	}

// Top-level declaration dispatcher

#[test]
def test_tag_hello : Bool :=
	match tag "hello" "hello world" {
		success rem out => String.beq rem " world",
		fail _ => false
	}

#[test]
def test_identifier_abc : Bool :=
	match identifier "abc def" {
		success rem out => String.beq out "abc" && String.beq rem " def",
		fail _ => false
	}

#[test]
def test_identifier_rejects_keyword : Bool :=
	match identifier "def x" {
		success _ _ => false,
		fail _ => true
	}

#[test]
def test_identifier_rejects_digit_start : Bool :=
	match identifier "123abc" {
		success _ _ => false,
		fail _ => true
	}

#[test]
def test_number_42 : Bool :=
	match number "42 abc" {
		success rem out => I64.beq out 42 && String.beq rem " abc",
		fail _ => false
	}

/// Regression test for suffixed numeric literals: `33u64` used to
/// mis-parse as juxtaposed application (`app (lit 33 i64) (var "u64")`)
/// since `number_term` only ever built a bare i64 literal and left the
/// suffix as trailing text — a wrong AST rather than a parse failure, so
/// no `success`/`fail`-only test could have caught it. See
/// `numeric_literal`'s doc comment (lang/parser/number.mo).
#[test]
def test_numeric_literal_suffix_u64 : Bool :=
	match numeric_literal "33u64" {
		success rem out =>
			String.beq rem "" && (match out {
				Term.lit lit_val => match lit_val {
					Literal.num n suffix => I64.beq n 33 && (match suffix {
						NumSuffix.u64 => true,
						_ => false
					}),
					_ => false
				},
				_ => false
			}),
		fail _ => false
	}

/// Hex integer literal (`0xBADBEEF`) — see `numeric_literal_digits`'s
/// `0x`/`0X`-prefix try in `lang/parser/number.mo`.
#[test]
def test_numeric_literal_hex : Bool :=
	match numeric_literal "0xBADBEEF" {
		success rem out =>
			String.beq rem "" && (match out {
				Term.lit lit_val => match lit_val {
					Literal.num n suffix => I64.beq n 195935983 && (match suffix {
						NumSuffix.i64 => true,
						_ => false
					}),
					_ => false
				},
				_ => false
			}),
		fail _ => false
	}

/// Uppercase `0X` prefix variant.
#[test]
def test_numeric_literal_hex_uppercase_prefix : Bool :=
	match numeric_literal "0XFF" {
		success rem out =>
			String.beq rem "" && (match out {
				Term.lit lit_val => match lit_val {
					Literal.num n suffix => I64.beq n 255 && (match suffix {
						NumSuffix.i64 => true,
						_ => false
					}),
					_ => false
				},
				_ => false
			}),
		fail _ => false
	}

/// Hex literal with a numeric suffix (`0xFFu32`).
#[test]
def test_numeric_literal_hex_suffix : Bool :=
	match numeric_literal "0xFFu32" {
		success rem out =>
			String.beq rem "" && (match out {
				Term.lit lit_val => match lit_val {
					Literal.num n suffix => I64.beq n 255 && (match suffix {
						NumSuffix.u32 => true,
						_ => false
					}),
					_ => false
				},
				_ => false
			}),
		fail _ => false
	}

/// Negative hex literal (`-0x10`) — same leading-`-` handling as decimal.
#[test]
def test_numeric_literal_hex_negative : Bool :=
	match numeric_literal "-0x10" {
		success rem out =>
			String.beq rem "" && (match out {
				Term.lit lit_val => match lit_val {
					Literal.num n suffix => I64.beq n (I64.sub 0 16) && (match suffix {
						NumSuffix.i64 => true,
						_ => false
					}),
					_ => false
				},
				_ => false
			}),
		fail _ => false
	}

/// Regression test for float literals: `3.0` used to mis-parse through
/// the registered `.` infix operator (juxtaposed int-dot-int
/// application) rather than as one literal. Unsuffixed floats default
/// to f64 (mirrors `float_suffix_parser`'s default, itself mirroring the
/// Rust reference).
#[test]
def test_numeric_literal_float : Bool :=
	match numeric_literal "3.0" {
		success rem out =>
			String.beq rem "" && (match out {
				Term.lit lit_val => match lit_val {
					Literal.flt text suffix => String.beq text "3.0" && (match suffix {
						NumSuffix.f64 => true,
						_ => false
					}),
					_ => false
				},
				_ => false
			}),
		fail _ => false
	}

#[test]
def test_numeric_literal_float_suffix : Bool :=
	match numeric_literal "3.14f32" {
		success rem out =>
			String.beq rem "" && (match out {
				Term.lit lit_val => match lit_val {
					Literal.flt text suffix => String.beq text "3.14" && (match suffix {
						NumSuffix.f32 => true,
						_ => false
					}),
					_ => false
				},
				_ => false
			}),
		fail _ => false
	}

/// Regression test for negative literals — this language's only form of
/// unary minus (see `numeric_literal`'s doc comment for why there's no
/// separate unary-negation operator). Before this fix `atom_term` had no
/// way to parse a bare `-1` at all; `lang/parser.mo` and
/// `lang/elaborate.mo`'s own `sentinel := -1` couldn't be re-parsed by
/// the self-hosted parser.
#[test]
def test_numeric_literal_negative : Bool :=
	match numeric_literal "-1" {
		success rem out =>
			String.beq rem "" && (match out {
				Term.lit lit_val => match lit_val {
					Literal.num n _suffix => I64.beq n (-1),
					_ => false
				},
				_ => false
			}),
		fail _ => false
	}

/// Confirms the negative-literal fix doesn't break binary subtraction:
/// `a - 1` (spaced, the universal style for infix operators) must still
/// take the operator-application path, not get swallowed as `app a
/// (-1)` by `expr_rest_ws`'s juxtaposition-first attempt. The `-` must
/// be immediately followed by a digit with no whitespace to count as a
/// negative literal, so `"- 1"` (space before the digit) correctly
/// fails `numeric_literal` and falls through to operator parsing.
#[test]
def test_expr_subtraction_not_negative_literal : Bool :=
	let empty_ctx : List Identifier := List.empty in
	match expression empty_ctx "a - 1" {
		success rem out => String.beq rem "" && term_is_app_not_lit out,
		fail _ => false
	}

#[partial]
def term_is_app_not_lit (t : Term) : Bool :=
	match t {
		Term.app _ _ => true,
		_ => false
	}

#[test]
def test_number_fail_empty : Bool :=
	match number "abc" {
		success _ _ => false,
		fail _ => true
	}

#[test]
def test_alt_tag : Bool :=
	match (alt (tag "foo") (tag "bar")) "foobar" {
		success rem out => String.beq out "foo" && String.beq rem "bar",
		fail _ => false
	}

#[test]
def test_many1_single : Bool :=
	match many1 (tag "a") "a" {
		success rem out => String.beq rem "",
		fail _ => false
	}

#[test]
def test_many1_multiple : Bool :=
	match many1 (tag "a") "aaab" {
		success rem out => String.beq rem "b",
		fail _ => false
	}

#[test]
def test_many1_fail : Bool :=
	match many1 (tag "a") "b" {
		success _ _ => false,
		fail _ => true
	}

#[test]
def test_do_empty : Bool :=
    let empty_ctx : List Identifier := List.empty in
    match do_parser empty_ctx "do { }" {
        success rem _ => String.beq rem "",
        fail _ => false
    }

#[test]
def test_do_return : Bool :=
    let empty_ctx : List Identifier := List.empty in
    match do_parser empty_ctx "do { return 42 }" {
        success rem _ => String.beq rem "",
        fail _ => false
    }

#[test]
def test_do_bind : Bool :=
    let empty_ctx : List Identifier := List.empty in
    match do_parser empty_ctx "do { let x <- m; return x }" {
        success rem _ => String.beq rem "",
        fail _ => false
    }

#[test]
def test_do_let : Bool :=
    let empty_ctx : List Identifier := List.empty in
    match do_parser empty_ctx "do { let x := 1; return x }" {
        success rem _ => String.beq rem "",
        fail _ => false
    }

#[test]
def test_do_expr : Bool :=
    let empty_ctx : List Identifier := List.empty in
    match do_parser empty_ctx "do { println 42; return 0 }" {
        success rem _ => String.beq rem "",
        fail _ => false
    }

#[test]
def test_do_chain : Bool :=
    let empty_ctx : List Identifier := List.empty in
    match do_parser empty_ctx "do { let a <- f x; let b <- g a; return b }" {
        success rem _ => String.beq rem "",
        fail _ => false
    }

#[test]
def test_do_desugar_structure : Bool :=
    // Verify desugaring produces the right Term structure
    // do { return x }  →  app (var sentinel Monad.pure) x
    // But x is unbound, so it's var(sentinel, named "x")
    let empty_ctx : List Identifier := List.empty in
    match do_parser empty_ctx "do { return x }" {
        success rem out =>
            match out {
                app f a => String.beq rem "",
                _ => false
            },
        fail _ => false
    }

#[partial]
def id_str (s : String) : String := s

#[partial]
def str_len (s : String) : I64 := String.length s

#[partial]
def always_tag_y (a : String) (input : String) : ParseResult String := tag "y" input

#[test]
def test_map_parse_tag : Bool :=
	match map_parse id_str (tag "x") "xy" {
		success rem out => String.beq out "x",
		fail _ => false
	}

#[test]
def test_map_parse_fail : Bool :=
	match map_parse id_str (tag "x") "y" {
		success rem out => false,
		fail e => true
	}

// Was two near-duplicate tests (test_map_parse_simple/test_map_parse_mapped)
// on the same input through the same parser, neither checking the mapped
// output — merged into one that checks both the remaining input and the
// actual transformed value, exercising map_parse's polymorphism (String ->
// String vs String -> I64) with real signal instead of two weak copies.
#[test]
def test_map_parse_transforms_output : Bool :=
	match map_parse str_len identifier "abc def" {
		success rem out => String.beq rem " def" && I64.beq out 3,
		fail _ => false
	}

#[test]
def test_bind_parse : Bool :=
	match bind_parse (tag "x") always_tag_y "xyz" {
		success rem out => String.beq rem "z",
		fail _ => false
	}

#[test]
def test_bind_parse_fail_first : Bool :=
	match bind_parse (tag "x") always_tag_y "abc" {
		success rem out => false,
		fail e => true
	}

#[test]
def test_bind_parse_fail_second : Bool :=
	match bind_parse (tag "x") always_tag_y "xab" {
		success rem out => false,
		fail e => true
	}

#[test]
def test_alt_fold_first : Bool :=
	match alt_fold (List.cons (tag "a") (List.cons (tag "b") (List.cons (tag "c") List.empty))) "abc" {
		success rem out => String.beq rem "bc",
		fail _ => false
	}

#[test]
def test_alt_fold_second : Bool :=
	match alt_fold (List.cons (tag "x") (List.cons (tag "y") (List.cons (tag "z") List.empty))) "y" {
		success rem out => String.beq rem "",
		fail _ => false
	}

#[test]
def test_alt_fold_none : Bool :=
	match alt_fold (List.cons (tag "x") (List.cons (tag "y") List.empty)) "abc" {
		success rem out => false,
		fail e => true
	}

#[test]
def test_preceded_by : Bool :=
	match preceded_by (tag "(") (tag "x") "(x" {
		success rem out => String.beq rem "",
		fail _ => false
	}

#[test]
def test_preceded_by_fail : Bool :=
	match preceded_by (tag "(") (tag "x") "x" {
		success rem out => false,
		fail e => true
	}

#[test]
def test_terminated_by : Bool :=
	match terminated_by (tag "x") (tag ")") "x)" {
		success rem out => String.beq rem "",
		fail _ => false
	}

#[test]
def test_terminated_by_fail : Bool :=
	match terminated_by (tag "x") (tag ")") "x(" {
		success rem out => false,
		fail e => true
	}

#[test]
def test_delimited_by : Bool :=
	match delimited_by (tag "(") (tag "x") (tag ")") "(x)" {
		success rem out => String.beq rem "",
		fail _ => false
	}

#[test]
def test_delimited_by_fail_open : Bool :=
	match delimited_by (tag "(") (tag "x") (tag ")") "x)" {
		success rem out => false,
		fail e => true
	}

#[test]
def test_delimited_by_fail_close : Bool :=
	match delimited_by (tag "(") (tag "x") (tag ")") "(x(" {
		success rem out => false,
		fail e => true
	}

#[test]
def test_separated_by_single : Bool :=
	match separated_by (tag ",") (tag "a") "a" {
		success rem out => String.beq rem "",
		fail _ => false
	}

#[test]
def test_separated_by_multi : Bool :=
	match separated_by (tag ",") (tag "a") "a,a,a" {
		success rem out => String.beq rem "",
		fail _ => false
	}

#[test]
def test_separated_by_empty : Bool :=
	match separated_by (tag ",") (tag "a") "b" {
		success rem out => String.beq rem "b",
		fail e => false
	}

#[test]
def test_opt_some : Bool :=
	match opt (tag "x") "xy" {
		success rem out => match out {
			Option.some val => String.beq val "x",
			Option.none => false
		},
		fail _ => false
	}

#[test]
def test_opt_none : Bool :=
	match opt (tag "x") "yz" {
		success rem out => match out {
			Option.some val => false,
			Option.none => String.beq rem "yz"
		},
		fail _ => false
	}

#[test]
def test_ws0 : Bool :=
	match ws0 "  abc" {
		success rem out => String.beq rem "abc",
		fail _ => false
	}

#[test]
def test_ws0_empty : Bool :=
	match ws0 "abc" {
		success rem out => String.beq rem "abc",
		fail _ => false
	}

#[test]
def test_ws1 : Bool :=
	match ws1 "  abc" {
		success rem out => String.beq rem "abc",
		fail _ => false
	}

#[test]
def test_ws1_fail : Bool :=
	match ws1 "abc" {
		success rem out => false,
		fail e => true
	}

// --- Position tracking tests (Phase 1.2) ---

#[test]
def test_new_span : Bool :=
	let span : LocatedSpan := new_span "hello" in
	let frag : String := span_fragment span in
	I64.beq (String.length frag) 5

#[test]
def test_new_span_location : Bool :=
	let span : LocatedSpan := new_span "x" in
	let loc : Location := span_location span in
	match loc {
		mk off line col => I64.beq off 0 && I64.beq line 1 && I64.beq col 1
	}

#[test]
def test_consume_no_newline : Bool :=
	let span : LocatedSpan := new_span "hello world" in
	let next : LocatedSpan := consume_span span 5 in
	let loc : Location := span_location next in
	match loc {
		mk off line col => I64.beq off 5 && I64.beq line 1 && I64.beq col 6
	}

#[test]
def test_consume_single_newline : Bool :=
	let span : LocatedSpan := new_span "a\nb" in
	let next : LocatedSpan := consume_span span 2 in
	let loc : Location := span_location next in
	match loc {
		mk off line col => I64.beq off 2 && I64.beq line 2 && I64.beq col 1
	}

#[test]
def test_consume_multi_newline : Bool :=
	let span : LocatedSpan := new_span "a\n\nb" in
	let next : LocatedSpan := consume_span span 3 in
	let loc : Location := span_location next in
	match loc {
		mk off line col => I64.beq off 3 && I64.beq line 3 && I64.beq col 1
	}

/// Regression test for the `advance_location` bug found while activating
/// this dead code for `location_of_remaining`: consuming *past* a
/// newline (not stopping exactly at one, unlike every existing test
/// above) used to reset column to 1 and then ignore every character
/// after the last newline entirely — `"a\nbc"` produced column 1
/// instead of the correct 3.
#[test]
def test_consume_newline_then_more_chars : Bool :=
	let span : LocatedSpan := new_span "a\nbcd" in
	let next : LocatedSpan := consume_span span 4 in
	let loc : Location := span_location next in
	match loc {
		mk off line col => I64.beq off 4 && I64.beq line 2 && I64.beq col 3
	}

#[test]
def test_location_of_remaining_no_consumption : Bool :=
	let loc : Location := location_of_remaining "hello world" "hello world" in
	match loc {
		mk off line col => I64.beq off 0 && I64.beq line 1 && I64.beq col 1
	}

#[test]
def test_location_of_remaining_single_line : Bool :=
	let loc : Location := location_of_remaining "def add (a) : I64" ") : I64" in
	match loc {
		mk off line col => I64.beq off 10 && I64.beq line 1 && I64.beq col 11
	}

#[test]
def test_location_of_remaining_multi_line : Bool :=
	let loc : Location := location_of_remaining "def f :=\n  bad" "bad" in
	match loc {
		mk off line col => I64.beq off 11 && I64.beq line 2 && I64.beq col 3
	}

/// `location_of_remaining` must correctly account for a multi-byte
/// character already consumed when computing the column of what's left
/// — the same UTF-8 codepoint-vs-byte distinction `utf8_char_width`
/// fixed for scanning itself (lang/parser/combinators.mo).
#[test]
def test_location_of_remaining_utf8 : Bool :=
	let loc : Location := location_of_remaining "// — x" "x" in
	match loc {
		// "// — " is 5 *characters* (the em dash is 3 bytes but 1
		// character) even though it's 7 bytes, so column 6 (1-indexed),
		// not the byte-count-derived 8.
		mk off line col => I64.beq off 7 && I64.beq line 1 && I64.beq col 6
	}

#[test]
def test_span_fragment_after_consume : Bool :=
	let span : LocatedSpan := new_span "hello world" in
	let next : LocatedSpan := consume_span span 6 in
	let rest : String := span_fragment next in
	String.beq rest "world"

def sentinel : I64 := -1

#[partial]
def ident_str (id: Identifier) : String :=
    match id {
        id s => s
    }

#[partial]
def find_index (id: Identifier) (ctx: List Identifier) (depth: I64) : Option I64 :=
    match ctx {
        List.cons x rest =>
            if String.beq (ident_str id) (ident_str x)
            then Option.some depth
            else find_index id rest (depth + 1),
        List.empty => Option.none
    }

#[partial]
def debug_name_of_id (id: Identifier) : DebugName :=
    DebugName.named id

#[partial]
def var_term (ctx: List Identifier) (s: String) : Term :=
    let sid : Identifier := Identifier.id s in
    match find_index sid ctx 0 {
        Option.some idx => Term.var idx (DebugName.named sid),
        Option.none => Term.var sentinel (DebugName.named sid)
    }

#[partial]
def variable (ctx: List Identifier) (input: String) : ParseResult Term :=
    variable_try_path (path_variable input) ctx input

#[partial]
def variable_try_path (r: ParseResult TermV0) (ctx: List Identifier) (input: String) : ParseResult Term :=
    match r {
        success rem out =>
            // Dotted path → sentinel index (resolved later by module resolver)
            // Extract the last component of the qualified name for constructor detection
            match out {
                TermV0.var nref =>
                    match name_ref_to_string nref {
                        Option.some qualified_name =>
                            // Preserve the full qualified name for proper resolution
                            // is_constructor_var will extract the base name if needed
                            success rem (Term.var sentinel (DebugName.named (Identifier.id qualified_name))),
                        Option.none =>
                            success rem (Term.var sentinel DebugName.unnamed),
                    },
                _ =>
                    success rem (Term.var sentinel DebugName.unnamed),
            },
        fail _ => variable_got (identifier input) ctx
    }

#[partial]
def variable_got (r: ParseResult String) (ctx: List Identifier) : ParseResult Term :=
    match r {
        success rem out => success rem (var_term ctx out),
        fail e => fail e
    }

// ─── Canonical literal parser (Phase 10) ───────────────────────────────

// `numeric_literal` (lang.parser.number) handles the full
// `[-]digits[.digits][suffix]` shape — int/float, sign, and suffix all
// in one parser. See its doc comment for why the sign lives here rather
// than as a separate unary-minus operator.
#[partial]
def literal_parser (input: String) : ParseResult Term :=
    alt_fold [string_parse, numeric_literal] input

// Skip // and /// comment lines (consumed as whitespace). Named
// `skip_docstrings` for historical reasons (it originally only matched
// `///`), but a bare `tag "///"` left plain `//` header/inline comments
// unconsumed — anything from `//` onward would then hit `decl_parser` as
// if it were a declaration and fail, which (before `decls_try`'s
// resync fix) silently truncated the rest of the file's decl_list. Matching
// on `"//"` (a prefix of `"///"` too) skips both forms uniformly.
#[partial]
def skip_docstrings (input : String) : String :=
	skip_docstrings_try (tag "//" input) input

#[partial]
def skip_docstrings_try (r : ParseResult String) (orig : String) : String :=
	match r {
		success rem _ => skip_docstrings_eol (take_while is_not_newline rem) rem,
		fail _ => orig
	}

#[partial]
def skip_docstrings_eol (r : ParseResult String) (orig : String) : String :=
	let after_eol : String := skip_spaces_match r orig in
	skip_docstrings_try_newline (tag "\n" after_eol) after_eol

#[partial]
def skip_docstrings_try_newline (r : ParseResult String) (orig : String) : String :=
	match r {
		success rem _ => skip_docstrings (skip_spaces rem),
		fail _ => orig
	}

// ─── Term atom ──────────────────────────────────────────────────────────

#[partial]
// ─── General `let ... in ...` term (previously do-block-only) ─────────
//
// `let name [: Type] := value in body` desugars to an immediately-
// applied lambda (`(fn name : Type => body) value`, mirroring the Rust
// reference's `lets()`/`let_term()`, core/src/term.rs) — no new `Term`
// variant needed, this is purely a parser-level construction, same as
// `lambda_parser`'s own `fn`/`ꟛ`/`\` desugaring right below it.
//
// Previously `let` was ONLY ever recognized inside `do { }` blocks
// (`do_stmt_try_let` above) — as a general expression usable anywhere a
// term is expected (a def's body, inside `if`/`then`/`else` branches,
// inside match arms, ...) it was entirely unparseable by this
// self-hosted parser, despite being the single most common expression
// form in the whole corpus (including this very file's own source, and
// `lang/json.mo`/`lang/toml.mo`, whose truncated self-hosted parse this
// fix was found while chasing down). Multiple chained `let`s
// (`let a := 1 in let b := 2 in body`) fall out for free from ordinary
// recursion — `body` below is a general `expression`, which can itself
// be another `let_term_parser` match — matching how virtually all real
// code writes multi-binding lets anyway (one `let ... in` per line, not
// the Rust grammar's `many1`-per-single-`let` alternative shape).
#[partial]
def let_term_parser (ctx : List Identifier) (input : String) : ParseResult Term :=
    let_term_kw (tag "let" input) ctx

#[partial]
def let_term_kw (r : ParseResult String) (ctx : List Identifier) : ParseResult Term :=
    match r {
        success rem _ => let_term_name (identifier (skip_spaces rem)) ctx,
        fail e => fail e
    }

/// Tries `:=` (no type annotation) BEFORE `:` (annotation present) —
/// not the other way around. `:` is a literal prefix of `:=`, so
/// checking `:` first would wrongly "match" the leading colon of a
/// bare `:=` too (`tag ":" ":= 1"` succeeds, leaving `"= 1"` — which
/// then fails trying to parse `=` as a type expression). Trying `:=`
/// first is unambiguous either way: it only matches when there's
/// genuinely no annotation (`: T := v` doesn't start with the two
/// characters `:=`, so this attempt correctly fails and falls through).
#[partial]
def let_term_name (r : ParseResult String) (ctx : List Identifier) : ParseResult Term :=
    match r {
        success rem name => let_term_try_assign_no_type (tag ":=" (skip_spaces rem)) rem (Identifier.id name) ctx,
        fail e => fail e
    }

#[partial]
def let_term_try_assign_no_type (r : ParseResult String) (orig : String) (name : Identifier) (ctx : List Identifier) : ParseResult Term :=
    match r {
        success rem _ => let_term_value (expression ctx (skip_docstrings (skip_spaces rem))) name Term.hole ctx,
        fail _ => let_term_try_type (tag ":" (skip_spaces orig)) orig name ctx
    }

#[partial]
def let_term_try_type (r : ParseResult String) (orig : String) (name : Identifier) (ctx : List Identifier) : ParseResult Term :=
    match r {
        success rem _ => let_term_type (type_expression ctx rem) name ctx,
        fail e => fail (ParseError.custom "expected ':' or ':=' in let expression" (parse_error_remaining e))
    }

#[partial]
def let_term_type (r : ParseResult Term) (name : Identifier) (ctx : List Identifier) : ParseResult Term :=
    match r {
        success rem typ => let_term_assign (tag ":=" (skip_spaces rem)) name typ ctx,
        fail e => fail e
    }

#[partial]
def let_term_assign (r : ParseResult String) (name : Identifier) (typ : Term) (ctx : List Identifier) : ParseResult Term :=
    match r {
        success rem _ => let_term_value (expression ctx (skip_docstrings (skip_spaces rem))) name typ ctx,
        fail e => fail (ParseError.custom "expected := in let expression" (parse_error_remaining e))
    }

#[partial]
def let_term_value (r : ParseResult Term) (name : Identifier) (typ : Term) (ctx : List Identifier) : ParseResult Term :=
    match r {
        // `skip_docstrings (skip_spaces rem)` -- a comment can sit right
        // before `in` too, not only after it.
        success rem value => let_term_in (tag "in" (skip_docstrings (skip_spaces rem))) name typ value ctx,
        fail e => fail e
    }

#[partial]
def let_term_in (r : ParseResult String) (name : Identifier) (typ : Term) (value : Term) (ctx : List Identifier) : ParseResult Term :=
    match r {
        success rem _ => let_term_body (expression (List.cons name ctx) (skip_docstrings (skip_spaces rem))) name typ value,
        fail e => fail (ParseError.custom "expected 'in' in let expression" (parse_error_remaining e))
    }

#[partial]
def let_term_body (r : ParseResult Term) (name : Identifier) (typ : Term) (value : Term) : ParseResult Term :=
    match r {
        success rem body =>
            let lam_term : Term := Term.lam (DebugName.named name) typ body in
            success rem (Term.app lam_term value),
        fail e => fail e
    }

// ─── List literal (`[e1, e2, e3]`) ──────────────────────────────────────
//
// Desugars to `FromListLiteral.cons e1 (FromListLiteral.cons e2
// (FromListLiteral.cons e3 FromListLiteral.empty))` — a right fold using
// the `FromListLiteral` class's methods (`init/prelude.mo`), not the raw
// `List.cons`/`List.empty` constructors directly, exactly mirroring the
// Rust reference's `desugar_list_literal` (core/src/parser.rs). Bracket
// syntax (`[`) was previously only ever recognized for class/instance
// `[Constraint A]` clauses (`class_try_constraints`/
// `instance_try_constraints`) — as a general term/expression, list
// literals were entirely unparseable by this self-hosted parser, despite
// being used constantly throughout the corpus (including this very
// file's own `op_table`/`decl_parsers`/`atom_parsers` list literals).
// `Term.var sentinel (DebugName.named (Identifier.id "..."))` for a
// qualified free-variable reference mirrors `variable_try_path`'s own
// representation for a dotted path (`Foo.bar` as one joined
// `Identifier`, not a structured `ModulePath`) — the established
// convention elsewhere in this file, not a new one invented here.
#[partial]
def list_literal_parser (ctx : List Identifier) (input : String) : ParseResult Term :=
    list_literal_open (tag "[" input) ctx

#[partial]
def list_literal_open (r : ParseResult String) (ctx : List Identifier) : ParseResult Term :=
    match r {
        success rem _ =>
            let empty_acc : List Term := List.empty in
            list_literal_elements (skip_spaces rem) ctx empty_acc,
        fail e => fail e
    }

#[partial]
def list_literal_elements (input : String) (ctx : List Identifier) (acc : List Term) : ParseResult Term :=
    match tag "]" input {
        success rem _ => success rem (build_list_literal (list_reverse acc)),
        fail _ => list_literal_element (expression ctx input) ctx acc
    }

#[partial]
def list_literal_element (r : ParseResult Term) (ctx : List Identifier) (acc : List Term) : ParseResult Term :=
    match r {
        success rem elem => list_literal_sep (skip_spaces rem) ctx (List.cons elem acc),
        fail e => fail e
    }

/// A trailing comma before `]` is optional (`[1, 2, 3,]` and
/// `[1, 2, 3]` both valid) — mirrors the Rust reference's
/// `opt(char(','))`.
#[partial]
def list_literal_sep (input : String) (ctx : List Identifier) (acc : List Term) : ParseResult Term :=
    match tag "," input {
        success rem _ => list_literal_elements (skip_spaces rem) ctx acc,
        fail _ => list_literal_close (tag "]" input) acc
    }

#[partial]
def list_literal_close (r : ParseResult String) (acc : List Term) : ParseResult Term :=
    match r {
        success rem _ => success rem (build_list_literal (list_reverse acc)),
        fail e => fail e
    }

#[partial]
def build_list_literal (elems : List Term) : Term :=
    match elems {
        List.empty => Term.var sentinel (DebugName.named (Identifier.id "FromListLiteral.empty")),
        List.cons e rest =>
            let cons_var : Term := Term.var sentinel (DebugName.named (Identifier.id "FromListLiteral.cons")) in
            Term.app (Term.app cons_var e) (build_list_literal rest),
    }

// ─── Struct-literal parser (`{ field := value, ... [: TypeExpr] }`) ────
//
// Mirrors the Rust reference's `struct_or_update_parser`/
// `struct_val_field_parser` (core/src/parser.rs) — a bare `{` atom
// distinct from `struct`'s own DECLARATION syntax (`field : Type`, no
// `:=`) and from `do { ... }` (which requires the literal keyword `do`
// before its own `{`, so there's no grammar collision with a bare `{`
// atom here). `StructUpdate` (`{ base with field := v, ... }`, tried
// FIRST — see `struct_update_try` just below) IS implemented, parsing
// into a real `Literal.struct_update` — this comment used to say
// "deliberately not implemented", which was true when it was written
// but has since landed; `lang/typecheck/infer.mo`'s
// `type_check_struct_update` desugars it into an ordinary `Term.con`
// (mirroring plain struct literals, just below), so it compiles too.
#[partial]
def struct_lit_parser (ctx: List Identifier) (input: String) : ParseResult Term :=
    struct_lit_open (tag "{" input) ctx

#[partial]
def struct_lit_open (r : ParseResult String) (ctx : List Identifier) : ParseResult Term :=
    match r {
        success rem _ => struct_update_try (variable ctx (skip_docstrings (skip_spaces rem))) ctx rem,
        fail e => fail e
    }

/// `{ base with field := value, ... }` is tried FIRST (mirrors the
/// reference's own `alt((parse_struct_update, ...))` ordering,
/// `struct_or_update_parser`, core/src/parser.rs) — if `base` parses as
/// a variable but no literal `with` keyword follows, this is an
/// ordinary struct literal whose first field's NAME happens to also be
/// a valid bare variable reference (e.g. `{ x := 1 }`'s `x`); back off
/// entirely to `orig` (right after the opening `{`) and parse it as
/// such, discarding whatever `variable` matched.
#[partial]
def struct_update_try (r : ParseResult Term) (ctx : List Identifier) (orig : String) : ParseResult Term :=
    match r {
        success rem base => struct_update_with (tag "with" (skip_docstrings (skip_spaces rem))) ctx base orig,
        fail _ =>
            let empty_acc : List StructLitField := List.empty in
            struct_lit_fields (skip_docstrings (skip_spaces orig)) ctx empty_acc,
    }

#[partial]
def struct_update_with (r : ParseResult String) (ctx : List Identifier) (base : Term) (orig : String) : ParseResult Term :=
    match r {
        success rem _ =>
            let empty_acc : List StructLitField := List.empty in
            struct_update_fields (skip_docstrings (skip_spaces rem)) ctx base empty_acc,
        fail _ =>
            let empty_acc : List StructLitField := List.empty in
            struct_lit_fields (skip_docstrings (skip_spaces orig)) ctx empty_acc,
    }

#[partial]
def struct_update_fields (input : String) (ctx : List Identifier) (base : Term) (acc : List StructLitField) : ParseResult Term :=
    match struct_lit_field ctx input {
        success rem field => struct_update_field_sep (skip_docstrings (skip_spaces rem)) ctx base (List.cons field acc),
        fail _ => struct_update_finish input base (list_reverse acc)
    }

/// A trailing comma before the closing `}` is optional, same as
/// `struct_lit_field_sep`.
#[partial]
def struct_update_field_sep (input : String) (ctx : List Identifier) (base : Term) (acc : List StructLitField) : ParseResult Term :=
    match tag "," input {
        success rem _ => struct_update_fields (skip_docstrings (skip_spaces rem)) ctx base acc,
        fail _ => struct_update_finish input base (list_reverse acc)
    }

/// Unlike `struct_lit_close`, there is no trailing `: TypeExpr`
/// self-annotation for a struct update — `base`'s own type already
/// determines the result type. Mirrors `parse_struct_update`
/// (core/src/parser.rs), which closes directly with `}`.
#[partial]
def struct_update_finish (input : String) (base : Term) (fields : List StructLitField) : ParseResult Term :=
    match tag "}" (skip_docstrings (skip_spaces input)) {
        success rem _ => success rem (Term.lit (Literal.struct_update base fields)),
        fail e => fail (ParseError.custom "expected } to close struct update" input)
    }

#[partial]
def struct_lit_fields (input : String) (ctx : List Identifier) (acc : List StructLitField) : ParseResult Term :=
    match struct_lit_field ctx input {
        success rem field => struct_lit_field_sep (skip_docstrings (skip_spaces rem)) ctx (List.cons field acc),
        fail _ => struct_lit_close input (list_reverse acc)
    }

/// A trailing comma before the closing `}`/`:` is optional, same as the
/// list-literal parser's own `list_literal_sep`.
#[partial]
def struct_lit_field_sep (input : String) (ctx : List Identifier) (acc : List StructLitField) : ParseResult Term :=
    match tag "," input {
        success rem _ => struct_lit_fields (skip_docstrings (skip_spaces rem)) ctx acc,
        fail _ => struct_lit_close input (list_reverse acc)
    }

#[partial]
def struct_lit_field (ctx : List Identifier) (input : String) : ParseResult StructLitField :=
    match identifier input {
        success rem name => struct_lit_field_eq (tag ":=" (skip_docstrings (skip_spaces rem))) ctx (Identifier.id name),
        fail e => fail e
    }

#[partial]
def struct_lit_field_eq (r : ParseResult String) (ctx : List Identifier) (name : Identifier) : ParseResult StructLitField :=
    match r {
        success rem _ => struct_lit_field_val (expression ctx (skip_docstrings (skip_spaces rem))) name,
        fail e => fail e
    }

#[partial]
def struct_lit_field_val (r : ParseResult Term) (name : Identifier) : ParseResult StructLitField :=
    match r {
        success rem value => success rem (StructLitField.mk name value),
        fail e => fail e
    }

/// After the field list: an optional `: TypeExpr` self-annotation, then
/// the mandatory closing `}`.
#[partial]
def struct_lit_close (input : String) (fields : List StructLitField) : ParseResult Term :=
    match tag ":" (skip_docstrings (skip_spaces input)) {
        success rem _ => struct_lit_type_name (type_expression List.empty (skip_docstrings (skip_spaces rem))) fields,
        fail _ =>
            let none_typ : Option Term := Option.none in
            struct_lit_finish input fields none_typ
    }

#[partial]
def struct_lit_type_name (r : ParseResult Term) (fields : List StructLitField) : ParseResult Term :=
    match r {
        success rem typ => struct_lit_finish rem fields (Option.some typ),
        fail e => fail e
    }

#[partial]
def struct_lit_finish (input : String) (fields : List StructLitField) (type_name : Option Term) : ParseResult Term :=
    match tag "}" (skip_docstrings (skip_spaces input)) {
        success rem _ => success rem (Term.lit (Literal.struct_lit fields type_name)),
        fail e => fail (ParseError.custom "expected } to close struct literal" input)
    }

#[partial]
def atom_term (ctx: List Identifier) (input: String) : ParseResult Term :=
    match alt_fold (atom_parsers ctx) input {
        success rem out => success rem out,
        fail _ =>
            match lambda_parser ctx input {
                success rem out => success rem out,
                fail _ => paren_expr ctx input
            }
    }

// ─── `quote { <term> }` (syntax as data) ────────────────────────────────
//
// Mirrors the Rust reference's `quote_parser` (core/src/parser.rs):
// `"quote"` keyword, mandatory whitespace, `{`, one full (unrestricted)
// term, `}`. Parsing/representation only -- see `Term.quote_`'s own doc
// comment in lang/types.mo for what's deliberately NOT done here yet
// (no expansion, `unquote` resolution, or hygiene). `quote` is already
// a reserved word in this parser's own keyword list (`kw_list`,
// lang/parser/core.mo) -- `identifier` (lang/parser/identifier.mo)
// already rejects it, so there's no ambiguity between this atom and a
// bare-`quote`-named variable to worry about; nothing needed here
// beyond adding the new atom parser itself.
#[partial]
def quote_term_parser (ctx: List Identifier) (input: String) : ParseResult Term :=
    quote_term_kw (tag "quote" input) ctx

#[partial]
def quote_term_kw (r : ParseResult String) (ctx : List Identifier) : ParseResult Term :=
    match r {
        success rem _ => quote_term_ws1 (ws1 rem) ctx,
        fail e => fail e
    }

#[partial]
def quote_term_ws1 (r : ParseResult String) (ctx : List Identifier) : ParseResult Term :=
    match r {
        success rem _ => quote_term_open (tag "{" rem) ctx,
        fail e => fail e
    }

#[partial]
def quote_term_open (r : ParseResult String) (ctx : List Identifier) : ParseResult Term :=
    match r {
        success rem _ => quote_term_body (expression ctx (skip_spaces rem)),
        fail e => fail e
    }

#[partial]
def quote_term_body (r : ParseResult Term) : ParseResult Term :=
    match r {
        success rem t => quote_term_finish (tag "}" (skip_spaces rem)) t rem,
        fail e => fail e
    }

#[partial]
def quote_term_finish (r : ParseResult String) (t : Term) (orig : String) : ParseResult Term :=
    match r {
        success rem _ => success rem (Term.quote_ t),
        fail e => fail (ParseError.custom "expected } to close quote" orig)
    }

// ─── Term-position `name!` (`foo!`, `foo! 1 2`) ─────────────────────────
//
// Mirrors the Rust reference's `macro_call` (core/src/parser.rs):
// `identifier` immediately (no space) followed by `!`. Produces
// `Term.var_macro` -- see that variant's own doc comment in
// lang/types.mo. `foo! 1 2` then falls out of the ordinary
// application-of-atoms machinery already in this file for free, once
// `foo!` itself parses as one atom -- no separate application-level
// change needed, unlike the reference's own `application` parser
// (which explicitly lists `macro_call` as a function-head alternative
// alongside `variable`) purely because self-hosted's own atom-then-
// juxtaposed-application loop already treats every atom uniformly this
// way.
//
// MUST be tried before `variable ctx` in `atom_parsers` below -- this
// is the one place in the whole metaprogramming-grammar plan where
// alternation order is load-bearing for *correctness*, not just style.
// `variable ctx` alone would happily match just `foo` on input
// `foo! 1 2`, leaving `! 1 2` unconsumed -- which the operator-
// precedence climber would then try (and typically fail, or worse,
// silently misparse against some unrelated `!`-prefixed grammar) to
// consume as a trailing infix operator, rather than this atom ever
// getting a chance to recognize the whole `foo!` token. See this
// file's own `test_macro_call_term_ordering_hazard_is_real` for a
// standalone repro proving this isn't a hypothetical.
#[partial]
def macro_call_term (input : String) : ParseResult Term :=
    macro_call_term_name (identifier input)

#[partial]
def macro_call_term_name (r : ParseResult String) : ParseResult Term :=
    match r {
        success rem name => macro_call_term_bang (tag "!" rem) name,
        fail e => fail e
    }

#[partial]
def macro_call_term_bang (r : ParseResult String) (name : String) : ParseResult Term :=
    match r {
        success rem _ => success rem (Term.var_macro sentinel (DebugName.named (Identifier.id name))),
        fail e => fail e
    }

#[partial]
def atom_parsers (ctx: List Identifier) : List (String -> ParseResult Term) :=
    // `do_parser` wires do-notation blocks (`do { ... }`) into the generic
    // expression grammar -- without it, `do { ... }` is only reachable via
    // a *keyword-less* bare `{ ... }` special case in a def/instance-method
    // body (see `def_body_block_or_none`/`instance_method_body_block_or_expr`),
    // never as a nested expression (an if/then/else branch, a match-arm
    // body, or an explicit `:= do { ... }` def body) -- see
    // `plans/bootstrapping/self-hosted-compiler.md` for the corpus impact
    // this had (137 real `do {` usages across lang/main.mo and
    // lang/module.mo, all previously unparseable).
    [quote_term_parser ctx, macro_call_term, variable ctx, literal_parser, match_parser ctx, if_parser ctx, do_parser ctx, let_term_parser ctx, list_literal_parser ctx, struct_lit_parser ctx]

// ─── Canonical match case parser (Phase 9) ─────────────────────────────

#[partial]
def match_case_parser (ctx: List Identifier) (input: String) : ParseResult MatchCase :=
    match_case_name (dotted_identifier (skip_docstrings (skip_spaces input))) ctx

/// A match case's constructor may be written qualified with its type name
/// (`Identifier.id as => ...`) or bare (`id as => ...`) — both are common
/// in practice. Constructors are stored and looked up by their bare name
/// alone (`InductConstructor.mk`'s own `name` is never type-prefixed, see
/// `type_cons_*`), so only the last dotted segment is kept; the type-name
/// qualifier, if present, is accepted but not otherwise meaningful here.
/// Previously a bare `identifier` was used, so ANY qualified constructor
/// pattern failed to parse at all — this blocked lang/types.mo itself
/// (`match a { Identifier.id as => ... }`), a self-hosting blocker.
#[partial]
def match_case_name (r: ParseResult (List String)) (ctx: List Identifier) : ParseResult MatchCase :=
    match r {
        success rem names =>
            match_case_args (match_case_arg_names rem) (Identifier.id (list_last_or "" names)) ctx,
        fail e => fail e
    }

/// Last element of a non-empty `List String`, or `default` if empty.
#[partial]
def list_last_or (default : String) (xs : List String) : String := match xs {
    List.empty => default,
    List.cons x rest => if List.is_empty rest then x else list_last_or default rest,
}

/// The constructor's bound-variable names (`List.cons x rest => ...`
/// binds `x` and `rest`) — zero or more space-separated identifiers
/// before `=>`. Previously `many0 identifier (skip_spaces rem)` only
/// skipped whitespace ONCE, before the *first* identifier attempt, not
/// between each one `many0` itself tries — since `identifier` doesn't
/// skip its own leading whitespace, that meant any pattern with 2+
/// bound names (`List.cons x rest`, the single most common shape in
/// this entire codebase) could only ever parse the first one, silently
/// leaving " rest => ..." dangling and then failing at the `=>` tag
/// right after — this was a genuine self-hosted-parser blocker, not
/// specific to any one file (confirmed: `list_rev_loop`'s own canonical
/// `List.cons x rest => ...` pattern, straight out of lang/types.mo,
/// failed to parse via this self-hosted parser before this fix).
#[partial]
def match_case_arg_names (input : String) : ParseResult (List String) :=
    match_case_arg_names_loop input List.empty

#[partial]
def match_case_arg_names_loop (input : String) (acc : List String) : ParseResult (List String) :=
    match identifier (skip_spaces input) {
        success rem name => match_case_arg_names_loop rem (List.cons name acc),
        fail _ => success input (list_reverse acc)
    }

#[partial]
def match_case_args (r: ParseResult (List String)) (name: Identifier) (ctx: List Identifier) : ParseResult MatchCase :=
    match r {
        // `skip_docstrings (skip_spaces rem)` -- a comment can sit right
        // before `=>` too (documenting a case's binder args), not only
        // right after it (`match_case_arrow`'s own fix, above).
        success rem names => match_case_arrow (tag "=>" (skip_docstrings (skip_spaces rem))) name (id_list_of names) ctx,
        fail e => fail e
    }

#[partial]
def id_list_of (names : List String) : List Identifier :=
    match names {
        List.cons n rest => List.cons (Identifier.id n) (id_list_of rest),
        List.empty => List.empty,
    }

/// Extends `ctx` with `args` (via `lambda_extend_ctx` — same "last
/// name = innermost = index 0" fold `lambda_extend_ctx`'s own doc
/// comment describes, and the exact convention
/// `lang/typecheck/infer.mo`'s `prepend_holes`/`prepend_local_vars`
/// independently use when building the matching `LocalScope`/
/// `local_types` for typecheck — both sides have to agree on the same
/// ordering or a body reference resolves to the WRONG bound variable
/// instead of just failing loudly) before parsing the arm's body —
/// otherwise a match arm's body referencing its own bound names
/// (`mk name _ _ => name`, `examples/optics.mo`'s own `get_name`)
/// resolves `name` as an unbound free variable instead of a properly-
/// indexed bound one: it still PARSES (free-variable references are
/// never a parse error), but fails to self-hosted-typecheck.
#[partial]
def match_case_arrow (r: ParseResult String) (name: Identifier) (args : List Identifier) (ctx: List Identifier) : ParseResult MatchCase :=
    match r {
        // `skip_docstrings (skip_spaces rem)`, not bare `skip_spaces rem`
        // -- a `//`/`///` comment right after `=>`, before the arm's body
        // expression (e.g. an inline comment documenting the branch about
        // to be taken), must be skipped like whitespace here too, same as
        // `match_cases_parse`'s own comment-between-arms fix elsewhere in
        // this file.
        success rem _ => match_case_body (expression (lambda_extend_ctx args ctx) (skip_docstrings (skip_spaces rem))) name args,
        fail e => fail e
    }

/// `args`, parsed by `match_case_arg_names` above, are threaded into
/// the final `MatchCase.mc` for real now — a previous version always
/// hardcoded an empty list here regardless of what was actually parsed,
/// silently dropping the constructor's bound-variable names (used
/// downstream by `lang/typecheck/infer.mo`'s `type_check_match_case` to
/// bind them as locals, and by `lang/pretty.mo`'s printer).
#[partial]
def match_case_body (r: ParseResult Term) (name: Identifier) (args : List Identifier) : ParseResult MatchCase :=
    match r {
        success rem body =>
            success (match_case_tail rem) (MatchCase.mc name args body),
        fail e => fail e
    }

/// Skips a trailing `,` after a match arm's body, plus any whitespace
/// AND `//`/`///` comments before the next arm (or the closing `}`) —
/// previously only `skip_spaces`, which left a comment line's `//`
/// sitting right where `match_case_parser`'s next attempt (or
/// `match_cases_parse`'s `}` check) expected a case pattern or the
/// closing brace, breaking on ANY comment between match arms
/// (unrelated to UTF-8 — a plain-ASCII `// comment` reproduces it too).
/// Found via `check_file`/`decls_parser_strict` failing to strict-parse
/// `lang/parser/combinators.mo`'s own `utf8_char_width`, which has
/// exactly this shape.
#[partial]
def match_case_tail (input: String) : String :=
    match take_while is_space input {
        success after_sp _ =>
            match tag "," after_sp {
                success rem _ => skip_docstrings (skip_spaces rem),
                fail _ => after_sp
            },
        fail _ => input
    }

// ─── Canonical match expression parser (Phase 9) ───────────────────────

#[partial]
def match_parser (ctx: List Identifier) (input: String) : ParseResult Term :=
    match_kw (tag "match" input) ctx

#[partial]
def match_kw (r: ParseResult String) (ctx: List Identifier) : ParseResult Term :=
    match r {
        success rem _ => match_scrutinee (expression ctx (skip_docstrings (skip_spaces rem))) ctx,
        fail e => fail e
    }

#[partial]
def match_scrutinee (r: ParseResult Term) (ctx: List Identifier) : ParseResult Term :=
    match r {
        success rem scrutinee => match_brace_open (tag "{" (skip_spaces rem)) scrutinee ctx,
        fail e => fail e
    }

#[partial]
def match_brace_open (r: ParseResult String) (scrutinee: Term) (ctx: List Identifier) : ParseResult Term :=
    match r {
        success rem _ => match_cases_parse (many1 (match_case_parser ctx) rem) scrutinee,
        fail e => fail e
    }

#[partial]
def match_cases_parse (r: ParseResult (List MatchCase)) (scrutinee: Term) : ParseResult Term :=
    match r {
        success rem cases => match_close (tag "}" (skip_docstrings (skip_spaces rem))) scrutinee cases,
        fail e => fail e
    }

#[partial]
def match_close (r: ParseResult String) (scrutinee: Term) (cases: List MatchCase) : ParseResult Term :=
    match r {
        success rem _ => success rem (Term.lit (Literal.match_ scrutinee cases)),
        fail e => fail e
    }

// ─── Canonical if expression parser (Phase 9) ─────────────────────────

#[partial]
def if_parser (ctx: List Identifier) (input: String) : ParseResult Term :=
    if_kw (tag "if" input) ctx

// `skip_docstrings (skip_spaces rem)`, not bare `skip_spaces rem`, at each
// of `if`/`then`/`else`'s sub-expression entry points below -- a comment
// directly after any of these three keywords (documenting the condition,
// the then-branch, or the else-branch) must be skipped like whitespace
// here too, same as `match_case_arrow`'s/`match_cases_parse`'s own
// comment fixes elsewhere in this file.
#[partial]
def if_kw (r: ParseResult String) (ctx: List Identifier) : ParseResult Term :=
    match r {
        success rem _ => if_cond (expression ctx (skip_docstrings (skip_spaces rem))) ctx,
        fail e => fail e
    }

// `skip_docstrings (skip_spaces rem)` before `tag "then"`/`tag "else"`
// too, not just after them -- a comment can sit right BEFORE the keyword
// itself (e.g. a `// Check base names` line documenting the next `else
// if` branch, lang/codegen/emit.mo's `constructor_tag`), not only right
// after it.
#[partial]
def if_cond (r: ParseResult Term) (ctx: List Identifier) : ParseResult Term :=
    match r {
        success rem cond => if_then_kw (tag "then" (skip_docstrings (skip_spaces rem))) cond ctx,
        fail e => fail e
    }

#[partial]
def if_then_kw (r: ParseResult String) (cond: Term) (ctx: List Identifier) : ParseResult Term :=
    match r {
        success rem _ => if_then_branch (expression ctx (skip_docstrings (skip_spaces rem))) cond ctx,
        fail e => fail e
    }

#[partial]
def if_then_branch (r: ParseResult Term) (cond: Term) (ctx: List Identifier) : ParseResult Term :=
    match r {
        success rem then_b => if_else_kw (tag "else" (skip_docstrings (skip_spaces rem))) cond then_b ctx,
        fail e => fail e
    }

#[partial]
def if_else_kw (r: ParseResult String) (cond: Term) (then_b: Term) (ctx: List Identifier) : ParseResult Term :=
    match r {
        success rem _ => if_else_branch (expression ctx (skip_docstrings (skip_spaces rem))) cond then_b,
        fail e => fail e
    }

#[partial]
def if_else_branch (r: ParseResult Term) (cond: Term) (then_b: Term) : ParseResult Term :=
    match r {
        success rem else_b => success rem (Term.lit (Literal.if_ cond then_b else_b)),
        fail e => fail e
    }

#[partial]
def paren_expr (ctx: List Identifier) (input: String) : ParseResult Term :=
    match tag "(" input {
        success rem _ => paren_inner (type_expression ctx rem) ctx,
        fail e => fail e
    }

#[partial]
def paren_inner (r: ParseResult Term) (ctx : List Identifier) : ParseResult Term :=
    match r {
        success rem out => paren_try_ann (skip_spaces rem) out ctx,
        fail e => fail e
    }

/// Optional `: Type` type ascription inside parens (`(List.empty : List
/// String)`) — parsed and discarded, not attached to the returned term:
/// this self-hosted `Term` has no `Ann` variant (unlike the Rust
/// reference's `Term::Ann`, core/src/parser.rs's `ann_parser`), so
/// there's nowhere to attach it even if kept. Matches the established
/// "parse for correctness, discard since nothing downstream needs it"
/// pattern already used by `def_implicit_close` for implicit param
/// clauses. Real usage — `List.intercalate "," (List.empty : List
/// String)` in `lang/json.mo` — needs the ascription to disambiguate an
/// otherwise type-unconstrained polymorphic empty list, but only the
/// self-hosted parser's own AST loses that information; the Rust
/// reference retains and uses it during typecheck.
#[partial]
def paren_try_ann (input : String) (out : Term) (ctx : List Identifier) : ParseResult Term :=
    match tag ":" input {
        success rem _ => paren_ann_type (type_expression ctx (skip_docstrings (skip_spaces rem))) out,
        fail _ => paren_close (tag ")" input) out
    }

#[partial]
def paren_ann_type (r : ParseResult Term) (out : Term) : ParseResult Term :=
    match r {
        success rem _ => paren_close (tag ")" (skip_spaces rem)) out,
        fail e => fail e
    }

#[partial]
def paren_close (r: ParseResult String) (out: Term) : ParseResult Term :=
    match r {
        success rem _ => success rem out,
        fail e => fail e
    }

// ─── Term lambda ────────────────────────────────────────────────────────

/// `fn a b c => body` — multiple curried params sugar (mirrors the Rust
/// reference's `many1(lam_param)` + `lams()`, core/src/parser.rs/
/// term.rs) for `fn a => fn b => fn c => body`. Previously only a
/// single name was ever accepted (`lambda_name_outer_got` went straight
/// to `=>` after one `identifier`), so any multi-param lambda —
/// extremely common throughout the corpus, e.g. `std/map.mo`'s `fn r ka
/// va => ...` — failed to parse at all: `def_parser`/`decls_parser`
/// wouldn't even get partway through, since a failed lambda anywhere
/// inside an expression fails the whole enclosing declaration.
#[partial]
def lambda_parser (ctx: List Identifier) (input: String) : ParseResult Term :=
    lambda_kw (alt (alt (tag "fn") (tag "ꟛ")) (tag "\\") input) ctx

#[partial]
def lambda_kw (r: ParseResult String) (ctx: List Identifier) : ParseResult Term :=
    match r {
        success rem _ =>
            let empty_names : List Identifier := List.empty in
            lambda_names (skip_spaces rem) ctx empty_names,
        fail e => fail e
    }

#[partial]
def lambda_names (input : String) (ctx : List Identifier) (acc : List Identifier) : ParseResult Term :=
    match identifier input {
        success rem name => lambda_names (skip_spaces rem) ctx (List.cons (Identifier.id name) acc),
        fail _ => lambda_names_done input ctx acc
    }

#[partial]
def lambda_names_done (input : String) (ctx : List Identifier) (acc : List Identifier) : ParseResult Term :=
    if List.is_empty acc
    then fail (ParseError.custom "expected at least one lambda parameter" input)
    else lambda_arrow (tag "=>" input) (list_reverse acc) ctx

#[partial]
def lambda_arrow (r: ParseResult String) (names: List Identifier) (ctx: List Identifier) : ParseResult Term :=
    match r {
        success rem2 _ => lambda_body (expression (lambda_extend_ctx names ctx) (skip_docstrings (skip_spaces rem2))) names,
        fail e => fail e
    }

/// Prepends `names` (declaration order, e.g. `[a, b, c]`) so the
/// *last*-declared name (`c`, innermost lambda, index 0) ends up at
/// `ctx`'s own head — same "reversed = innermost first" convention
/// `ctx_of_params`'s own doc comment describes.
#[partial]
def lambda_extend_ctx (names : List Identifier) (ctx : List Identifier) : List Identifier :=
    match names {
        List.cons n rest => lambda_extend_ctx rest (List.cons n ctx),
        List.empty => ctx,
    }

#[partial]
def lambda_body (r: ParseResult Term) (names: List Identifier) : ParseResult Term :=
    match r {
        success rem body => success rem (build_nested_lambdas names body),
        fail e => fail e
    }

/// `[a, b, c]`, `body` → `fn a => (fn b => (fn c => body))` — mirrors
/// the Rust reference's `lams()` fold exactly (first param outermost).
#[partial]
def build_nested_lambdas (names : List Identifier) (body : Term) : Term :=
    match names {
        List.cons n rest => Term.lam (DebugName.named n) (Term.type_ 1) (build_nested_lambdas rest body),
        List.empty => body,
    }

// ─── Term expression (application + operators) ─────────────────────────
//
// Real precedence-climbing (a linear-time Pratt parser), threading a
// `min_prec` floor through the recursion:
// 1. Parse one atom as the left-hand side (expr_climb_first).
// 2. Repeatedly try to parse another atom and apply it (juxtaposition,
//    e.g. `f x y`) — expr_climb_rest/expr_climb_rest_next loop until
//    that fails.
// 3. Once no more bare atoms apply, look for an infix operator
//    (expr_climb_op/expr_climb_op_try). An operator with precedence 0
//    in op_table (core.mo) — not a recognized operator — or below the
//    current `min_prec` floor stops parsing here (expr_climb_op_prec)
//    without consuming it, so the caller (an outer, lower-precedence
//    level, or the caller of `expression` itself) can try to consume it
//    as something else.
// 4. Otherwise recurse for the right-hand side at a raised floor
//    (expr_climb_op_rhs_ws) — `prec + 1` for a left-associative operator
//    (so a further same-precedence operator immediately following is
//    left for the OUTER loop to pick up, producing left-associative
//    nesting) or `prec` unchanged for a right-associative one (so a
//    further same-precedence operator IS allowed into the RHS,
//    producing right-associative nesting) — op_table's right_assoc flag
//    (op_lookup_rassoc, core.mo) is finally consulted, previously never
//    was: this file used a naive "always recurse into a fresh top-level
//    `expression` call for the RHS" scheme that made EVERY operator
//    right-associative regardless of its declared associativity. This
//    directly miscompiled examples/hello.mo's `main` (three
//    left-associative `|>` in a row: `args |> List.last |> (...) |>
//    say_hello` parsed as `args |> (List.last |> (... |> say_hello))`,
//    an entirely different, nonsensical application structure) — not
//    just a `|>`-specific issue, this affects any chain of same-
//    precedence operators (e.g. `a - b - c`, `a && b && c`).
// 5. After combining lhs/op/rhs, loop back (expr_climb_rest) to check
//    for MORE operators at the SAME `min_prec` floor — needed for left-
//    associative chains to keep building leftward (step 4's raised
//    floor only limits what the RECURSIVE RHS call may consume, not
//    this level's own continuation).

#[partial]
def expression (ctx: List Identifier) (input: String) : ParseResult Term :=
    expr_climb ctx input 0

#[partial]
def expr_climb (ctx: List Identifier) (input: String) (min_prec: I64) : ParseResult Term :=
    expr_climb_first (atom_term ctx (skip_spaces input)) ctx min_prec

#[partial]
def expr_climb_first (r: ParseResult Term) (ctx: List Identifier) (min_prec: I64) : ParseResult Term :=
    match r {
        success rem lhs => expr_climb_rest rem lhs ctx min_prec,
        fail e => fail e
    }

#[partial]
def expr_climb_rest (input: String) (lhs: Term) (ctx: List Identifier) (min_prec: I64) : ParseResult Term :=
    expr_climb_rest_ws (take_while is_space input) lhs ctx min_prec

#[partial]
def expr_climb_rest_ws (r: ParseResult String) (lhs: Term) (ctx: List Identifier) (min_prec: I64) : ParseResult Term :=
    match r {
        success rem _ => expr_climb_rest_next (atom_term ctx rem) rem lhs ctx min_prec,
        fail e => fail e
    }

#[partial]
def expr_climb_rest_next (r: ParseResult Term) (input: String) (lhs: Term) (ctx: List Identifier) (min_prec: I64) : ParseResult Term :=
    match r {
        success rem rhs => expr_climb_rest rem (Term.app lhs rhs) ctx min_prec,
        fail _ => expr_climb_op input lhs ctx min_prec
    }

#[partial]
def expr_climb_op (input: String) (lhs: Term) (ctx: List Identifier) (min_prec: I64) : ParseResult Term :=
    expr_climb_op_try (operator_parse input) input lhs ctx min_prec

#[partial]
def expr_climb_op_try (r: ParseResult String) (input: String) (lhs: Term) (ctx: List Identifier) (min_prec: I64) : ParseResult Term :=
    match r {
        success rem op => expr_climb_op_prec input lhs op rem ctx min_prec,
        fail _ => success input lhs
    }

// `op_lookup_entry` walks `op_table` ONCE for `op`, yielding both
// precedence and associativity -- `expr_climb_op_rhs_ws` used to call
// `op_lookup_rassoc op op_table` separately for the SAME operator on the
// SAME call path, a second full table scan for no reason. Threading the
// looked-up `rassoc` through as a parameter instead removes it.
#[partial]
def expr_climb_op_prec (input: String) (lhs: Term) (op: String) (rem: String) (ctx: List Identifier) (min_prec: I64) : ParseResult Term :=
    match op_lookup_entry op op_table {
        Option.none => success input lhs,
        Option.some entry =>
            let prec : I64 := op_entry_prec entry in
            if I64.lt prec min_prec
            then success input lhs
            else expr_climb_op_rhs_ws (take_while is_space rem) lhs op ctx prec (op_entry_rassoc entry) min_prec
    }

#[partial]
def expr_climb_op_rhs_ws (r: ParseResult String) (lhs: Term) (op: String) (ctx: List Identifier) (prec: I64) (rassoc: Bool) (min_prec: I64) : ParseResult Term :=
    match r {
        success rem _ =>
            let next_min : I64 := if rassoc then prec else (prec + 1) in
            expr_climb_op_rhs_expr (expr_climb ctx rem next_min) lhs op ctx min_prec,
        fail e => fail e
    }

/// `|>`/`<|` are pure syntactic sugar for application (`x |> f` = `f x`,
/// `f <| x` = `f x`) -- desugar them DIRECTLY to `Term.app`, not through
/// the generic operator desugaring below.
///
/// The generic path used to build `Term.var sentinel DebugName.unnamed`,
/// throwing `op` away entirely — `DebugName` has no operator-carrying
/// variant (unlike the Rust reference's own `NameRef::Op`, core/src/
/// term.rs) to preserve it in, so nothing downstream could ever recover
/// which operator an application like this meant; every `infix (op) :=
/// target` declaration (init/init.mo, init/prelude.mo) was consequently
/// unreachable from a parsed operator application, and even built-in
/// arithmetic (`n + 1`) silently compiled to a `Unit` placeholder.
///
/// Fixed by preserving the operator SYMBOL as the var's own name
/// (`DebugName.named (Identifier.id op)`) — a deliberate "fake
/// identifier" (operator symbols can never appear as a bare identifier
/// from ordinary parsing, so this can't collide with a real one) that's
/// never re-parsed as source text, only ever looked up by
/// `lang.scope`'s new `resolve_infix_decls` pass (`ScopeData.infixes`,
/// itself already populated from every loaded module's `infix`
/// declarations, was sitting unused until this fix) once a real Scope
/// is available -- parsing alone doesn't know what `+`/`==`/a custom
/// operator ultimately resolves to, only scope-building does.
#[partial]
def expr_climb_op_rhs_expr (r: ParseResult Term) (lhs: Term) (op: String) (ctx: List Identifier) (min_prec: I64) : ParseResult Term :=
    match r {
        success rem rhs =>
            let combined : Term :=
                if String.beq op "|>"
                then Term.app rhs lhs
                else if String.beq op "<|"
                then Term.app lhs rhs
                else
                    // Operator desugars to: op lhs rhs → app (app (var SENTINEL op) lhs) rhs
                    let op_var : Term := Term.var sentinel (DebugName.named (Identifier.id op)) in
                    Term.app (Term.app op_var lhs) rhs
            in
            expr_climb_rest rem combined ctx min_prec,
        fail e => fail e
    }

// ─── Term type expression (like expression but with -> for pi) ─────────

#[partial]
def type_expression (ctx: List Identifier) (input: String) : ParseResult Term :=
    type_expr_ws (take_while is_space input) input ctx

#[partial]
def type_expr_ws (r: ParseResult String) (input: String) (ctx: List Identifier) : ParseResult Term :=
    match r {
        success rem _ => type_try_dep (tag "(" (skip_spaces rem)) input ctx,
        fail e => fail e
    }

#[partial]
def type_try_dep (r: ParseResult String) (input: String) (ctx: List Identifier) : ParseResult Term :=
    match r {
        success rem _ => type_dep_id (identifier (skip_spaces rem)) input ctx,
        fail _ => type_plain input ctx
    }

#[partial]
def type_dep_id (r: ParseResult String) (input: String) (ctx: List Identifier) : ParseResult Term :=
    match r {
        success rem name => type_dep_colon (tag ":" (skip_spaces rem)) input name ctx,
        fail _ => type_plain input ctx
    }

#[partial]
def type_dep_colon (r: ParseResult String) (input: String) (name: String) (ctx: List Identifier) : ParseResult Term :=
    match r {
        success rem _ => type_dep_typ (type_expression ctx (skip_docstrings (skip_spaces rem))) input name ctx,
        fail _ => type_plain input ctx
    }

#[partial]
def type_dep_typ (r: ParseResult Term) (input: String) (name: String) (ctx: List Identifier) : ParseResult Term :=
    match r {
        success rem typ => type_dep_close (tag ")" (skip_spaces rem)) input name typ ctx,
        fail _ => type_plain input ctx
    }

#[partial]
def type_dep_close (r: ParseResult String) (input: String) (name: String) (typ: Term) (ctx: List Identifier) : ParseResult Term :=
    match r {
        success rem _ => type_dep_arrow rem name typ ctx,
        fail _ => type_plain input ctx
    }

#[partial]
def type_dep_arrow (rem: String) (name: String) (typ: Term) (ctx: List Identifier) : ParseResult Term :=
    type_dep_arrow_ws (take_while is_space rem) rem name typ ctx

#[partial]
def type_dep_arrow_ws (r: ParseResult String) (rem: String) (name: String) (typ: Term) (ctx: List Identifier) : ParseResult Term :=
    match r {
        success rem2 _ => type_dep_arrow_tag (tag "->" rem2) rem name typ ctx,
        fail e => fail e
    }

#[partial]
def type_dep_arrow_tag (r: ParseResult String) (rem: String) (name: String) (typ: Term) (ctx: List Identifier) : ParseResult Term :=
    match r {
        success rem2 _ => type_dep_body (type_expression (List.cons (Identifier.id name) ctx) (skip_docstrings (skip_spaces rem2))) typ,
        fail _ => success rem typ
    }

#[partial]
def type_dep_body (r: ParseResult Term) (typ: Term) : ParseResult Term :=
    match r {
        success rem body => success rem (Term.pi typ body),
        fail e => fail e
    }

// Plain type expression (no dependent binding on LHS).

// Parses expression, then checks for non-dependent -> arrow.

#[partial]
def type_plain (input: String) (ctx: List Identifier) : ParseResult Term :=
    type_plain_expr (expression ctx input) ctx

#[partial]
def type_plain_expr (r: ParseResult Term) (ctx: List Identifier) : ParseResult Term :=
    match r {
        success rem lhs => type_check_arrow rem lhs ctx,
        fail e => fail e
    }

#[partial]
def type_check_arrow (input: String) (lhs: Term) (ctx: List Identifier) : ParseResult Term :=
    type_arrow_ws (take_while is_space input) input lhs ctx

#[partial]
def type_arrow_ws (r: ParseResult String) (input: String) (lhs: Term) (ctx: List Identifier) : ParseResult Term :=
    match r {
        success rem _ => type_arrow_tag (tag "->" rem) input lhs ctx,
        fail e => fail e
    }

#[partial]
def type_arrow_tag (r: ParseResult String) (input: String) (lhs: Term) (ctx: List Identifier) : ParseResult Term :=
    match r {
        success rem _ => type_arrow_rhs lhs (type_expression ctx (skip_docstrings (skip_spaces rem))),
        fail _ => success input lhs
    }

#[partial]
def type_arrow_rhs (lhs: Term) (r: ParseResult Term) : ParseResult Term :=
    match r {
        success rem rhs => success rem (Term.pi lhs rhs),
        fail e => fail e
    }

// ─── Phase 1.5: docstring and implicit params tests ───────────────────────────────

#[test]
def test_skip_docstrings_none : Bool :=
	let rem : String := skip_docstrings "use prelude" in
	String.beq rem "use prelude"

#[test]
def test_skip_docstrings_one : Bool :=
	let rem : String := skip_docstrings "/// doc\nuse prelude" in
	String.beq rem "use prelude"

#[test]
def test_skip_docstrings_multi : Bool :=
	let rem : String := skip_docstrings "/// line1\n/// line2\n\ndef x := 1" in
	String.beq rem "def x := 1"

/// Regression test for the UTF-8 byte-vs-codepoint stepping bug
/// (`utf8_char_width`, lang/parser/combinators.mo): a multi-byte
/// character (an em dash, 3 bytes in UTF-8) inside a comment used to
/// make `take_while`-based scanning silently stop right there —
/// `String.slice`/`String.drop` both fall back to "" once the byte
/// offset lands mid-character, indistinguishable from genuine
/// end-of-input. Directly mirrors `lang/json.mo`/`lang/toml.mo`'s own
/// blocked first declaration (an em dash in a doc comment before it).
#[test]
def test_skip_docstrings_utf8_em_dash : Bool :=
	let rem : String := skip_docstrings "/// an em dash — right here\ndef x := 1" in
	String.beq rem "def x := 1"

/// Same bug, but inside a string literal's plain (non-escaped) content
/// rather than a comment — exercises `string_body_loop`'s own
/// `utf8_char_width` stepping (lang/parser/string.mo).
#[test]
def test_string_parse_utf8_em_dash : Bool :=
	match string_parse "\"an em dash — right here\"" {
		success rem out => String.beq rem "" && term_lit_str_eq out "an em dash — right here",
		fail _ => false
	}

#[test]
def test_decls_with_docstring : Bool :=
	match decls_parser "/// A test declaration\ndef x : I64 := 42" {
		success rem decl_list =>
			let rem_stripped : String := skip_spaces rem in
			String.beq rem_stripped "" && I64.beq (debug_decl_count decl_list) 1,
		fail _ => false
	}

#[test]
def test_type_implicit_params : Bool :=
	match type_parser "type Any { any {A : Type} (value : A) }" {
		success rem decl => String.beq rem "",
		fail _ => false
	}

/// Regression test for `type_cons_group_more_names`: multiple
/// constructor-field names sharing one type in a single group
/// (`buckets (b0 b1 b2 : I64)`) — real usage: `std/map.mo`'s
/// `Buckets16` constructor (16 names, one type). Previously each field
/// group only accepted a single name, hard-failing the whole
/// declaration on the second name.
#[test]
def test_type_constructor_multi_name_group : Bool :=
	match type_parser "type Buckets3 { buckets (b0 b1 b2 : I64) }" {
		success rem decl => String.beq rem "",
		fail _ => false
	}

/// Regression test for `type_cons_one_group_content`'s missing
/// `skip_spaces`: a newline right after a constructor field group's
/// opening `(` (before the first field name) — real usage:
/// `std/map.mo`'s `Buckets16` constructor writes its opening paren and
/// first field name on separate lines. Pre-existing bug (not introduced
/// by the multi-name fix above), just never previously exercised by any
/// single-line test.
#[test]
def test_type_constructor_group_leading_newline : Bool :=
	match type_parser "type Buckets3 { buckets (\n  b0 b1 b2 : I64) }" {
		success rem decl => String.beq rem "",
		fail _ => false
	}

/// Regression test for `type_cons_group_colon`'s backtrack-to-bare-type
/// fallback: `map (Buckets16 K V)` — a bare/unnamed field whose type is
/// itself a multi-identifier application — looks exactly like "several
/// field names with no type" until the trailing `:` check fails; the
/// multi-name loop above must then re-parse the WHOLE thing as a bare
/// type expression from where the field started, not hard-fail. Real
/// usage: `std/map.mo`'s `HashMap` constructor.
#[test]
def test_type_constructor_bare_multi_word_type : Bool :=
	match type_parser "type HashMap K V { map (Buckets16 K V) }" {
		success rem decl => String.beq rem "",
		fail _ => false
	}

#[test]
def test_type_implicit_no_parens : Bool :=
	match type_parser "type All { mk {A : Type} (val : A) }" {
		success rem decl => String.beq rem "",
		fail _ => false
	}

// --- def-level implicit param clause tests ---
// `{A: Type}`'s content is intentionally discarded (see
// `def_implicit_close`'s doc comment) — these check that the def's
// EXPLICIT params still come through correctly afterward, not just that
// parsing doesn't crash.

#[test]
def test_def_implicit_single_name : Bool :=
	match def_parser "def id {A : Type} (x : A) : A := x" {
		success rem out => match out {
			def_d d => match d {
				Def.mk _name _typ term _constraints _attrs _vis => match term {
					Term.lam dbg _ptyp _body => Similar.similar dbg (DebugName.named (Identifier.id "x")),
					_ => false,
				}
			},
			_ => false,
		},
		fail _ => false
	}

#[test]
def test_def_implicit_multi_name : Bool :=
	match def_parser "def create_node {K V : Type} (key : K) (val : V) : K := key" {
		success rem out => match out {
			def_d d => match d {
				Def.mk _name _typ term _constraints _attrs _vis =>
					// Exactly the two EXPLICIT params should have made it
					// through as lambdas — {K V : Type}'s two names must
					// not have leaked in as extra bindings.
					match term {
						Term.lam dbg1 _ inner => outer_binding_ok dbg1 inner,
						_ => false,
					}
			},
			_ => false,
		},
		fail _ => false
	}

#[partial]
def outer_binding_ok (dbg1 : DebugName) (inner : Term) : Bool :=
	Similar.similar dbg1 (DebugName.named (Identifier.id "key")) && inner_binding_ok inner

#[partial]
def inner_binding_ok (t : Term) : Bool := match t {
	Term.lam dbg2 _ body =>
		Similar.similar dbg2 (DebugName.named (Identifier.id "val")) && is_body_non_lambda body,
	_ => false,
}

#[partial]
def is_body_non_lambda (t : Term) : Bool := match t {
	Term.lam _ _ _ => false,
	_ => true,
}

// --- TypeConstraint parsing tests ---

#[test]
def test_type_constraint_one_simple : Bool :=
	match type_constraint_one "Functor F" {
		success rem _ => String.beq rem "",
		fail _ => false
	}

#[test]
def test_type_constraint_one_two_vars : Bool :=
	match type_constraint_one "HAdd A A A" {
		success rem _ => String.beq rem "",
		fail _ => false
	}

#[test]
def test_type_constraint_one_no_vars : Bool :=
	match type_constraint_one "Show" {
		success rem _ => String.beq rem "",
		fail _ => false
	}

#[test]
def test_type_constraint_list_single : Bool :=
	match type_constraint_list "Functor F" {
		success rem _ => String.beq rem "",
		fail _ => false
	}

#[test]
def test_type_constraint_list_multi : Bool :=
	match type_constraint_list "Functor F, Applicative M" {
		success rem _ => String.beq rem "",
		fail _ => false
	}

#[test]
def test_type_constraint_list_empty : Bool :=
	match type_constraint_list "" {
		success rem _ => String.beq rem "",
		fail _ => false
	}

/// Strengthened beyond a bare `success` check: `class_close` used to
/// hardcode an empty constraint list regardless of what was actually
/// parsed (see `class_params`'s doc comment) — a test that only checked
/// `success`/`rem == ""` couldn't have caught that.
#[test]
def test_class_with_constraints : Bool :=
	match class_parser "class [Functor F] Applicative F { def pure (a : A) : F A }" {
		success rem out =>
			String.beq rem "" && (match out {
				class_d c => class_has_one_functor_f_constraint c,
				_ => false
			}),
		fail _ => false
	}

#[partial]
def class_has_one_functor_f_constraint (c : Class) : Bool :=
	match c {
		Class.mk _name _params constraints _methods _vis =>
			match constraints {
				List.cons tc rest => constraint_is_functor_f tc && list_is_empty_tc rest,
				List.empty => false
			}
	}

#[partial]
def constraint_is_functor_f (tc : TypeConstraint) : Bool :=
	match tc {
		TypeConstraint.mk cls vars =>
			Similar.similar cls (ModulePath.mp (List.cons (Identifier.id "Functor") List.empty))
				&& (match vars {
					List.cons v _ => Similar.similar v (Identifier.id "F"),
					List.empty => false
				})
	}

#[partial]
def list_is_empty_tc (cs : List TypeConstraint) : Bool :=
	match cs {
		List.empty => true,
		List.cons _ _ => false
	}

#[test]
def test_instance_with_constraints : Bool :=
  match instance_parser "instance [Show A] Show A { def m := a }" {
    success rem _ => String.beq rem "",
    fail _ => false
  }

/// Regression test for `skip_one_attr`: an attributed instance method
/// (`#[terminating] def ... := ...`) — previously broke the ENTIRE
/// enclosing `instance` block, since `instance_methods` skipped
/// docstrings but not `#[...]` attributes before checking for `def`.
/// Real usage: `std/map.mo`'s `instance [BOrd K] Map BTreeMap { ...
/// #[terminating] def insert ... }`.
#[test]
def test_instance_method_with_attribute : Bool :=
  match instance_parser "instance Show A { #[terminating] def m := a }" {
    success rem _ => String.beq rem "",
    fail _ => false
  }

/// Regression test for the `instance {Param : Type} Class ...` implicit
/// binder (unlike `def`'s implicit params, these are captured for real —
/// see `instance_implicit_params_loop`'s doc comment).
#[test]
def test_instance_implicit_params : Bool :=
	match instance_parser "instance {A : Type} Show A { def show x := x }" {
		success rem out =>
			String.beq rem "" && (match out {
				instance_d i => instance_has_one_param_named_A i,
				_ => false
			}),
		fail _ => false
	}

#[partial]
def instance_has_one_param_named_A (i : Instance) : Bool :=
	match i {
		Instance.mk _name _cls _constraints _args _vis implicit_params =>
			match implicit_params {
				List.cons p rest => param_named_A p && list_is_empty rest,
				List.empty => false
			}
	}

#[partial]
def param_named_A (p : Param) : Bool :=
	match p {
		Param.mk pname _typ _mult _default _attrs => Similar.similar pname (Identifier.id "A")
	}

#[partial]
def list_is_empty (ps : List Param) : Bool :=
	match ps {
		List.empty => true,
		List.cons _ _ => false
	}

/// Multi-name implicit clause `{K V : Type}` — both names should produce
/// their own `Param`, sharing the type (mirrors `test_def_implicit_multi_name`
/// but, unlike that test, both names must actually survive into the AST).
#[test]
def test_instance_implicit_params_multi_name : Bool :=
	match instance_parser "instance {K V : Type} Show K { def show x := x }" {
		success rem out =>
			String.beq rem "" && (match out {
				instance_d i => instance_has_two_params_named_K_V i,
				_ => false
			}),
		fail _ => false
	}

#[partial]
def instance_has_two_params_named_K_V (i : Instance) : Bool :=
	match i {
		Instance.mk _name _cls _constraints _args _vis implicit_params =>
			match implicit_params {
				List.cons p1 rest1 =>
					match rest1 {
						List.cons p2 rest2 =>
							param_named_K p1 && param_named_V p2 && list_is_empty rest2,
						List.empty => false
					},
				List.empty => false
			}
	}

#[partial]
def param_named_K (p : Param) : Bool :=
	match p {
		Param.mk pname _typ _mult _default _attrs => Similar.similar pname (Identifier.id "K")
	}

#[partial]
def param_named_V (p : Param) : Bool :=
	match p {
		Param.mk pname _typ _mult _default _attrs => Similar.similar pname (Identifier.id "V")
	}

#[test]
/// Strengthened beyond a bare `success` check — same rationale as
/// `test_class_with_constraints`: `class_close` used to hardcode an
/// empty *params* list too, regardless of what `(F : Type -> Type)`
/// actually parsed.
#[test]
def test_class_with_paren_params : Bool :=
  match class_parser "class Functor (F : Type -> Type) { def map (f : A -> B) : F A -> F B }" {
    success rem out =>
      String.beq rem "" && (match out {
        class_d c => class_has_one_param_named_F c,
        _ => false
      }),
    fail _ => false
  }

#[partial]
def class_has_one_param_named_F (c : Class) : Bool :=
	match c {
		Class.mk _name params _constraints _methods _vis =>
			match params {
				List.cons p rest => param_named_F p && list_is_empty rest,
				List.empty => false
			}
	}

#[partial]
def param_named_F (p : Param) : Bool :=
	match p {
		Param.mk pname _typ _mult _default _attrs => Similar.similar pname (Identifier.id "F")
	}

/// Strengthened beyond a bare `success` check: verifies the `:= List`
/// default actually reaches the parsed `Param`, not just that the whole
/// clause parses without error.
#[test]
def test_class_with_default_param : Bool :=
  match class_parser "class FromListLiteral (L : Type -> Type := List) { def cons (a : A) : L A -> L A }" {
    success rem out =>
      String.beq rem "" && (match out {
        class_d c => class_has_one_param_L_with_default c,
        _ => false
      }),
    fail _ => false
  }

#[partial]
def class_has_one_param_L_with_default (c : Class) : Bool :=
	match c {
		Class.mk _name params _constraints _methods _vis =>
			match params {
				List.cons p rest => param_named_L_with_default p && list_is_empty rest,
				List.empty => false
			}
	}

#[partial]
def param_named_L_with_default (p : Param) : Bool :=
	match p {
		Param.mk pname _typ _mult default _attrs =>
			Similar.similar pname (Identifier.id "L") && (match default {
				Option.some _ => true,
				Option.none => false
			})
	}

/// Regression test for the nested-parens bug: the previous param parser
/// used `take_while is_not_close_paren`, which stops at the *first* `)`
/// rather than the matching one — breaking outright on any nested paren
/// inside a class param's type. `std/map.mo`'s very first decl has this
/// exact shape.
#[test]
def test_class_with_nested_paren_param_type : Bool :=
  match class_parser "class Map (M: (K : Type) -> (V : Type) -> Type) { def empty : M K V }" {
    success rem _ => String.beq rem "",
    fail _ => false
  }

// ─── Term parser tests (Phase 1) ───────────────────────────────────────

#[test]
def test_t_var_bound : Bool :=
	let ctx : List Identifier := List.cons (Identifier.id "x") List.empty in
	match expression ctx "x" {
		success rem out =>
			match out {
				Term.var idx dbg =>
					I64.beq idx 0 && String.beq rem "",
				Term.lam _ _ _ => false, Term.forall _ _ _ => false,
				Term.pi _ _ => false, Term.app _ _ => false,
				Term.lit _ => false, Term.ntv _ => false,
				Term.con _ => false, Term.type_ _ => false, Term.hole => false
			},
		fail _ => false
	}

#[test]
def test_t_var_unbound : Bool :=
	let empty_ctx : List Identifier := List.empty in
	match expression empty_ctx "y" {
		success rem out =>
			match out {
				Term.var idx dbg =>
					I64.beq idx sentinel && String.beq rem "",
				Term.lam _ _ _ => false, Term.forall _ _ _ => false,
				Term.pi _ _ => false, Term.app _ _ => false,
				Term.lit _ => false, Term.ntv _ => false,
				Term.con _ => false, Term.type_ _ => false, Term.hole => false
			},
		fail _ => false
	}

#[test]
def test_t_var_shadow : Bool :=
	// In ctx [x, y, x] (outer x first), the inner x should be index 0
	let x : Identifier := Identifier.id "x" in
	let y : Identifier := Identifier.id "y" in
	let ctx : List Identifier := List.cons y (List.cons x (List.cons x List.empty)) in
	match expression ctx "x" {
		success rem out =>
			match out {
				Term.var idx dbg =>
					I64.beq idx 1 && String.beq rem "",
				Term.lam _ _ _ => false, Term.forall _ _ _ => false,
				Term.pi _ _ => false, Term.app _ _ => false,
				Term.lit _ => false, Term.ntv _ => false,
				Term.con _ => false, Term.type_ _ => false, Term.hole => false
			},
		fail _ => false
	}

#[test]
def test_t_lambda_identity : Bool :=
	// fn x => x  →  lam (named "x") (type_ 1) (var 0 (named "x"))
	let empty_ctx : List Identifier := List.empty in
	match expression empty_ctx "fn x => x" {
		success rem out =>
			match out {
				Term.lam dbg typ body =>
					match typ {
						Term.type_ u => I64.beq u 1 && String.beq rem "",
						Term.var _ _ => false, Term.lam _ _ _ => false,
						Term.forall _ _ _ => false, Term.pi _ _ => false,
						Term.app _ _ => false, Term.lit _ => false,
						Term.ntv _ => false, Term.con _ => false,
						Term.hole => false
					},
				Term.var _ _ => false, Term.forall _ _ _ => false,
				Term.pi _ _ => false, Term.app _ _ => false,
				Term.lit _ => false, Term.ntv _ => false,
				Term.con _ => false, Term.type_ _ => false, Term.hole => false
			},
		fail _ => false
	}

#[test]
def test_t_lambda_nested : Bool :=
	// fn x => fn y => y  →  lam/named/x (lam/named/y (var 0))
	let empty_ctx : List Identifier := List.empty in
	match expression empty_ctx "fn x => fn y => y" {
		success rem out => String.beq rem "",
		fail _ => false
	}

/// Regression test for `lambda_names`: `fn a b c => body` multi-param
/// sugar for `fn a => fn b => fn c => body` — previously only a single
/// name was ever accepted, blocking `std/map.mo`'s own `fn r ka va =>
/// ...` (extremely common throughout the corpus). Checks the SHAPE
/// nests correctly (3 lambdas deep), not just that it parses.
#[test]
def test_t_lambda_multi_param : Bool :=
	let empty_ctx : List Identifier := List.empty in
	match expression empty_ctx "fn a b c => a" {
		success rem out => String.beq rem "" && term_is_three_deep_lam out,
		fail _ => false
	}

#[partial]
def term_is_three_deep_lam (t : Term) : Bool :=
	match t {
		Term.lam _dbg1 _typ1 body1 =>
			match body1 {
				Term.lam _dbg2 _typ2 body2 =>
					match body2 {
						Term.lam _dbg3 _typ3 _body3 => true,
						_ => false
					},
				_ => false
			},
		_ => false
	}

#[test]
def test_t_app_simple : Bool :=
	// f x  →  app (var SENTINEL f) (var SENTINEL x)
	let empty_ctx : List Identifier := List.empty in
	match expression empty_ctx "f x" {
		success rem out => String.beq rem "",
		fail _ => false
	}

#[test]
def test_t_app_chain : Bool :=
	// f x y  →  app (app (var SENTINEL f) (var SENTINEL x)) (var SENTINEL y)
	let empty_ctx : List Identifier := List.empty in
	match expression empty_ctx "f x y" {
		success rem out => String.beq rem "",
		fail _ => false
	}

#[test]
def test_t_operator : Bool :=
	// a ++ b  →  app (app (var SENTINEL _) (var SENTINEL a)) (var SENTINEL b)
	let empty_ctx : List Identifier := List.empty in
	match expression empty_ctx "a ++ b" {
		success rem out => String.beq rem "",
		fail _ => false
	}

/// Regression test for the operator-resolution fix: the parsed term's
/// own head must now NAME the operator symbol itself
/// (`DebugName.named (Identifier.id "++")`), not `DebugName.unnamed` --
/// see `expr_climb_op_rhs_expr`'s own doc comment for why this is what
/// makes `lang.scope`'s `resolve_infix_decls` able to resolve it later.
#[test]
def test_t_operator_preserves_op_name : Bool :=
	let empty_ctx : List Identifier := List.empty in
	match expression empty_ctx "a ++ b" {
		success rem out =>
			String.beq rem "" &&
			match out {
				Term.app fun_outer _arg_outer =>
					match fun_outer {
						Term.app op_var _lhs =>
							match op_var {
								Term.var _ dbg =>
									match dbg {
										DebugName.named id => String.beq (show_identifier id) "++",
										DebugName.unnamed => false,
									},
								_ => false,
							},
						_ => false,
					},
				_ => false,
			},
		fail _ => false
	}

/// Regression test for expr_climb's precedence-climbing rewrite:
/// `a |> f |> g` must parse LEFT-associatively (matching `|>`'s
/// op_table entry, `OpEntry.mk "|>" 5 false`) as `g(f(a))` —
/// `App(g, App(f, a))` — not right-associatively as `f(g)(a)` (the
/// previous behavior: every operator recursed into a fresh top-level
/// `expression` call for its RHS, greedily consuming any FURTHER
/// same-precedence operator into that RHS regardless of op_table's
/// declared associativity). This exact shape — 3+ chained `|>` at the
/// same precedence — is examples/hello.mo's entire `main` function.
#[test]
def test_t_operator_chain_left_associative : Bool :=
	let empty_ctx : List Identifier := List.empty in
	match expression empty_ctx "a |> f |> g" {
		success rem out =>
			String.beq rem "" &&
			match out {
				Term.app fun_outer arg_outer =>
					match fun_outer {
						Term.var _ dbg_outer =>
							match dbg_outer {
								DebugName.named id_outer =>
									String.beq (show_identifier id_outer) "g" &&
									match arg_outer {
										Term.app fun_inner arg_inner =>
											match fun_inner {
												Term.var _ dbg_inner =>
													match dbg_inner {
														DebugName.named id_inner =>
															String.beq (show_identifier id_inner) "f" &&
															match arg_inner {
																Term.var _ dbg_a =>
																	match dbg_a {
																		DebugName.named id_a => String.beq (show_identifier id_a) "a",
																		DebugName.unnamed => false,
																	},
																_ => false,
															},
														DebugName.unnamed => false,
													},
												_ => false,
											},
										_ => false,
									},
								DebugName.unnamed => false,
							},
						_ => false,
					},
				_ => false,
			},
		fail _ => false
	}

#[test]
def test_t_parens : Bool :=
	// (x)  →  var (SENTINEL, x)
	let empty_ctx : List Identifier := List.empty in
	match expression empty_ctx "(x)" {
		success rem out => String.beq rem "",
		fail _ => false
	}

/// Regression test for `paren_try_ann`: a type ascription inside parens
/// (`(x : List I64)`) — previously unparseable, blocking real corpus
/// usage like `lang/json.mo`'s `(List.empty : List String)` (needed to
/// disambiguate an otherwise type-unconstrained polymorphic value).
#[test]
def test_t_paren_type_ascription : Bool :=
	let empty_ctx : List Identifier := List.empty in
	match expression empty_ctx "(x : List I64)" {
		success rem out => String.beq rem "",
		fail _ => false
	}

#[test]
def test_t_literal_num : Bool :=
	// 42  →  lit (num 42 i64)
	let empty_ctx : List Identifier := List.empty in
	match expression empty_ctx "42" {
		success rem out => String.beq rem "",
		fail _ => false
	}

#[test]
def test_match_simple : Bool :=
    let empty_ctx : List Identifier := List.empty in
    match match_parser empty_ctx "match x { some a => a, none => 0 }" {
        success rem out =>
            match out {
                lit val =>
                    match val {
                        match_ scrutinee cases => String.beq rem "",
                        _ => false
                    },
                _ => false
            },
        fail _ => false
    }

#[test]
def test_match_multi : Bool :=
    let empty_ctx : List Identifier := List.empty in
    match match_parser empty_ctx "match x { zero => 0, one => 1 }" {
        success rem out =>
            match out {
                lit val =>
                    match val {
                        match_ scrutinee cases => String.beq rem "",
                        _ => false
                    },
                _ => false
            },
        fail _ => false
    }

/// Regression test for `match_case_parser`/`match_case_tail`/
/// `match_cases_parse`: a `//` comment between two match arms (or right
/// after `{`, before the closing `}`) broke parsing — the case-parser
/// entry point and the post-comma tail both only skipped whitespace
/// (`skip_spaces`), never comments (`skip_docstrings`), so the `//`
/// itself was left as the "next thing" a case pattern or `}` needed to
/// match against. Unrelated to UTF-8/em-dashes specifically — any `//`
/// comment reproduces it. Found via `check_file`/`decls_parser_strict`
/// failing to strict-parse `lang/parser/combinators.mo`'s own
/// `utf8_char_width`, which has exactly this shape.
#[test]
def test_match_case_comment_between_arms : Bool :=
    let empty_ctx : List Identifier := List.empty in
    let src : String := "match x {\n\tzero => 0,\n\t// a comment right here\n\tone => 1\n}" in
    match match_parser empty_ctx src {
        success rem out =>
            match out {
                lit val =>
                    match val {
                        match_ scrutinee cases => String.beq rem "",
                        _ => false
                    },
                _ => false
            },
        fail _ => false
    }

/// Regression test for `match_case_arg_names`: a constructor pattern
/// binding 2+ names (`List.cons x rest => ...`, the single most common
/// match-arm shape in this entire codebase) used to only ever parse the
/// FIRST bound name — `many0 identifier (skip_spaces rem)` skipped
/// whitespace once before the first attempt, not between each one
/// `many0` itself tries, so anything past the first name (`rest`) was
/// left dangling and broke the subsequent `=>` match. Confirmed this
/// blocked `lang/types.mo`'s own canonical `list_rev_loop` from
/// re-parsing via the self-hosted parser.
#[test]
def test_match_case_multi_arg_pattern : Bool :=
    let empty_ctx : List Identifier := List.empty in
    match match_parser empty_ctx "match xs { List.cons x rest => 1, List.empty => 0 }" {
        success rem out => String.beq rem "",
        fail _ => false
    }

/// The parsed bound names must actually reach the resulting `MatchCase`
/// (a previous version hardcoded an empty `args` list regardless of
/// what `match_case_arg_names` parsed — used downstream by
/// `lang/typecheck/infer.mo`'s `type_check_match_case` to bind them as
/// locals).
#[test]
def test_match_case_arg_names_captured : Bool :=
    match match_case_parser List.empty "List.cons x rest => 1" {
        success rem out => String.beq rem "" && match_case_has_two_args out,
        fail _ => false
    }

#[partial]
def match_case_has_two_args (mc : MatchCase) : Bool :=
    match mc {
        MatchCase.mc _name args _body =>
            match args {
                List.cons a1 rest1 =>
                    match rest1 {
                        List.cons a2 rest2 =>
                            Similar.similar a1 (Identifier.id "x")
                                && Similar.similar a2 (Identifier.id "rest")
                                && (match rest2 { List.empty => true, _ => false }),
                        List.empty => false
                    },
                List.empty => false
            }
    }

/// Regression test for `match_case_arrow`'s `ctx` extension: a match
/// arm's body referencing one of its own bound names (`mk name _ _ =>
/// name`, `examples/optics.mo`'s own `get_name`) must resolve as a
/// properly-indexed BOUND variable (`Term.var <real index> ...`), not a
/// free one (`Term.var sentinel ...`) — the parse would "succeed"
/// either way (a free-variable reference is never a parse error), so
/// this checks the actual resolved index, not just success.
#[test]
def test_match_case_body_resolves_bound_name : Bool :=
    match match_case_parser List.empty "mk name other => name" {
        success rem out => String.beq rem "" && match_case_body_var_is_bound out,
        fail _ => false
    }

#[partial]
def match_case_body_var_is_bound (mc : MatchCase) : Bool :=
    match mc {
        MatchCase.mc _name _args body =>
            match body {
                Term.var idx _dbg => Bool.not (I64.beq idx sentinel),
                _ => false
            }
    }

#[test]
def test_if_simple : Bool :=
    let empty_ctx : List Identifier := List.empty in
    match if_parser empty_ctx "if true then 1 else 2" {
        success rem out =>
            match out {
                lit val =>
                    match val {
                        if_ cond then_b else_b => String.beq rem "",
                        _ => false
                    },
                _ => false
            },
        fail _ => false
    }

#[test]
def test_if_nested : Bool :=
    let empty_ctx : List Identifier := List.empty in
    match if_parser empty_ctx "if a then if b then 1 else 2 else 3" {
        success rem out =>
            match out {
                lit val =>
                    match val {
                        if_ cond then_b else_b => String.beq rem "",
                        _ => false
                    },
                _ => false
            },
        fail _ => false
    }

#[test]
def test_if_bound_var : Bool :=
    let x : Identifier := Identifier.id "x" in
    let ctx : List Identifier := List.cons x List.empty in
    match if_parser ctx "if x then 1 else x" {
        success rem out =>
            match out {
                lit val =>
                    match val {
                        if_ cond then_b else_b =>
                            String.beq rem "",
                        _ => false
                    },
                _ => false
            },
        fail _ => false
    }

/// Regression test for `let_term_parser`: a general `let name : Type :=
/// value in body` expression, usable anywhere a term is expected — not
/// just inside `do { }` blocks. Verifies it desugars to an
/// immediately-applied lambda (`(fn name : Type => body) value`, no new
/// `Term` variant), mirroring the Rust reference's `lets()`
/// (core/src/term.rs).
#[test]
def test_let_term_desugars_to_applied_lambda : Bool :=
    let empty_ctx : List Identifier := List.empty in
    match expression empty_ctx "let x : I64 := 1 in x" {
        success rem out => String.beq rem "" && term_is_app_of_lam out,
        fail _ => false
    }

#[partial]
def term_is_app_of_lam (t : Term) : Bool :=
    match t {
        Term.app fn_ _arg =>
            match fn_ {
                Term.lam _dbg _typ _body => true,
                _ => false
            },
        _ => false
    }

/// `let` with no type annotation, and usable as a def's entire body
/// (not wrapped in a `do` block) — both previously unparseable.
#[test]
def test_let_term_no_annotation_as_def_body : Bool :=
    match def_parser "def f (x : I64) : I64 :=\n  let y := x in\n  y" {
        success rem out => String.beq rem "" && (match out {
            def_d _ => true,
            _ => false
        }),
        fail _ => false
    }

/// Chained lets (`let a := ... in let b := ... in body`) fall out from
/// ordinary recursion — `let_term_body` parses a general `expression`,
/// which can itself be another `let`.
#[test]
def test_let_term_chained : Bool :=
    let empty_ctx : List Identifier := List.empty in
    match expression empty_ctx "let a := 1 in let b := 2 in a" {
        success rem out => String.beq rem "" && term_is_app_of_lam out,
        fail _ => false
    }

/// `let` inside an `if`/`then`/`else` branch — the exact shape that
/// blocked `lang/json.mo`'s own `Json.parse_string_char` from parsing.
#[test]
def test_let_term_inside_if_branch : Bool :=
    match def_parser "def f (x : I64) : I64 :=\n  if true\n  then x\n  else\n    let y := x in\n    y" {
        success rem out => String.beq rem "",
        fail _ => false
    }

/// Regression test for `list_literal_parser`: `[e1, e2, e3]` as a
/// general term — previously `[` was only ever recognized for class/
/// instance `[Constraint]` clauses, so list literals (used constantly
/// throughout the corpus, including this parser's own source) failed
/// to parse as an expression outright.
#[test]
def test_list_literal_desugars_to_cons_chain : Bool :=
    let empty_ctx : List Identifier := List.empty in
    match expression empty_ctx "[1, 2, 3]" {
        success rem out => String.beq rem "" && term_is_app_of_lam_or_var out,
        fail _ => false
    }

#[partial]
def term_is_app_of_lam_or_var (t : Term) : Bool :=
    match t {
        Term.app _fn_ _arg => true,
        _ => false
    }

#[test]
def test_list_literal_empty : Bool :=
    let empty_ctx : List Identifier := List.empty in
    match expression empty_ctx "[]" {
        success rem out => String.beq rem "",
        fail _ => false
    }

#[test]
def test_list_literal_trailing_comma : Bool :=
    let empty_ctx : List Identifier := List.empty in
    match expression empty_ctx "[1, 2, 3,]" {
        success rem out => String.beq rem "",
        fail _ => false
    }

/// The exact shape that blocked `lang/json.mo`'s own `op_table`-style
/// declarations from parsing: a function applied to a list-literal
/// argument (`h [1, 2, 3]`) — juxtaposed application must recognize `[`
/// as a valid atom start, not just a standalone expression.
#[test]
def test_list_literal_as_application_argument : Bool :=
    match def_parser "def f (input : String) : I64 :=\n  h [1, 2, 3]" {
        success rem out => String.beq rem "",
        fail _ => false
    }

/// Regression test for `struct_lit_parser`: `{ field := value, ... }`
/// as a general term — previously any bare `{` (outside `struct`'s own
/// DECLARATION syntax) was entirely unparseable as a value expression.
#[test]
def test_struct_lit_empty : Bool :=
    let empty_ctx : List Identifier := List.empty in
    match expression empty_ctx "{}" {
        success rem out => String.beq rem "" && term_is_struct_lit out,
        fail _ => false
    }

#[partial]
def term_is_struct_lit (t : Term) : Bool :=
    match t {
        Term.lit l => match l { Literal.struct_lit _ _ => true, _ => false },
        _ => false
    }

#[test]
def test_struct_lit_fields_no_annotation : Bool :=
    let empty_ctx : List Identifier := List.empty in
    match expression empty_ctx "{ x := 1, y := 2 }" {
        success rem out =>
            String.beq rem "" &&
            match out {
                Term.lit l => match l {
                    Literal.struct_lit fields type_name =>
                        I64.beq (List.length fields) 2 &&
                        match type_name { Option.none => true, Option.some _ => false },
                    _ => false
                },
                _ => false
            },
        fail _ => false
    }

#[test]
def test_struct_lit_trailing_comma_and_annotation : Bool :=
    let empty_ctx : List Identifier := List.empty in
    match expression empty_ctx "{ x := 1, y := 2, : Point }" {
        success rem out =>
            String.beq rem "" &&
            match out {
                Term.lit l => match l {
                    Literal.struct_lit fields type_name =>
                        I64.beq (List.length fields) 2 &&
                        match type_name { Option.some _ => true, Option.none => false },
                    _ => false
                },
                _ => false
            },
        fail _ => false
    }

/// A struct literal used as a function argument (juxtaposed
/// application) -- same shape check `list_literal_parser` needed
/// (`test_list_literal_as_application_argument`).
#[test]
def test_struct_lit_as_application_argument : Bool :=
    match def_parser "def f (input : String) : I64 :=\n  h { x := 1 }" {
        success rem out => String.beq rem "",
        fail _ => false
    }

/// Regression test for the struct-update alternative (`{ base with
/// field := value, ... }`, `struct_update_try`/`struct_update_with`):
/// previously only ordinary struct literals were parseable, so any
/// real `{ x with ... }` usage (e.g. examples/structs.mo's own
/// `test_struct_update`) failed to parse under this self-hosted
/// parser's own STRICT mode.
#[test]
def test_struct_update_basic : Bool :=
    let x : Identifier := Identifier.id "p1" in
    let ctx : List Identifier := List.cons x List.empty in
    match expression ctx "{ p1 with x := 10 }" {
        success rem out =>
            String.beq rem "" &&
            match out {
                Term.lit l => match l {
                    Literal.struct_update _base fields => I64.beq (List.length fields) 1,
                    _ => false
                },
                _ => false
            },
        fail _ => false
    }

/// A bare struct literal whose first field's NAME happens to also be a
/// valid variable reference (`x`) must NOT be misparsed as a
/// struct-update with no `with` -- confirms the backtrack-to-`orig`
/// fallback in `struct_update_try`/`struct_update_with` actually fires.
#[test]
def test_struct_update_backtrack_to_plain_literal : Bool :=
    let empty_ctx : List Identifier := List.empty in
    match expression empty_ctx "{ x := 1, y := 2 }" {
        success rem out =>
            String.beq rem "" &&
            match out {
                Term.lit l => match l {
                    Literal.struct_lit fields _ => I64.beq (List.length fields) 2,
                    _ => false
                },
                _ => false
            },
        fail _ => false
    }

// --- Tests for attribute_parser/attr_arg_parser/opt_attributes ---
// (IS wired into def_parser/type_parser -- see this file's own doc
// comment above `attribute_parser` -- these tests exercise the parser
// functions directly for finer-grained coverage than going through a
// full `def_parser`/`type_parser` call each time would give.)

#[test]
def test_attribute_parser_bare_name : Bool :=
    match attribute_parser "#[test]" {
        success rem attr =>
            String.beq rem "" &&
            match attr { Attribute.mk name args => id_eq name (Identifier.id "test") && I64.beq (List.length args) 0 },
        fail _ => false
    }

/// The real corpus shape (`#[derive BEq BOrd Debug Lens]`) is ONE
/// attribute with four bare-ident args, not four stacked attributes —
/// confirmed against the reference grammar this round.
#[test]
def test_attribute_parser_multi_ident_args : Bool :=
    match attribute_parser "#[derive BEq BOrd Debug Lens]" {
        success rem attr =>
            String.beq rem "" &&
            match attr {
                Attribute.mk name args =>
                    id_eq name (Identifier.id "derive") && I64.beq (List.length args) 4,
            },
        fail _ => false
    }

#[test]
def test_attribute_parser_string_and_num_args : Bool :=
    match attribute_parser "#[native \"foo\" 42]" {
        success rem attr =>
            String.beq rem "" &&
            match attr {
                Attribute.mk _ args => match args {
                    List.cons a1 rest =>
                        match a1 { AttrArg.str s => String.beq s "foo", _ => false } &&
                        match rest {
                            List.cons a2 _ => match a2 { AttrArg.num n => I64.beq n 42, _ => false },
                            List.empty => false,
                        },
                    List.empty => false,
                },
            },
        fail _ => false
    }

#[test]
def test_attribute_parser_unknown_input_fails : Bool :=
    match attribute_parser "not an attribute" {
        success _ _ => false,
        fail _ => true
    }

#[test]
def test_opt_attributes_stacked : Bool :=
    match opt_attributes "#[test]\n#[partial]\ndef foo" {
        success rem attrs =>
            String.beq rem "def foo" && I64.beq (List.length attrs) 2,
        fail _ => false
    }

#[test]
def test_opt_attributes_none_present : Bool :=
    match opt_attributes "def foo" {
        success rem attrs => String.beq rem "def foo" && I64.beq (List.length attrs) 0,
        fail _ => false
    }

// --- Tests for real attribute capture wired into def_parser/type_parser ---

#[test]
def test_def_parser_captures_test_attribute : Bool :=
    match def_parser "#[test]\ndef foo (x : I64) : I64 := x" {
        success rem out =>
            String.beq rem "" &&
            match out {
                Decl.def_d d => match d {
                    Def.mk _ _ _ _ attrs _ =>
                        I64.beq (List.length attrs) 1 && has_attr (Identifier.id "test") attrs,
                },
                _ => false
            },
        fail _ => false
    }

/// A plain (unattributed) def must still parse with an empty attrs
/// list, exactly as before this round's change.
#[test]
def test_def_parser_no_attribute_present : Bool :=
    match def_parser "def foo (x : I64) : I64 := x" {
        success rem out =>
            String.beq rem "" &&
            match out {
                Decl.def_d d => match d {
                    Def.mk _ _ _ _ attrs _ => I64.beq (List.length attrs) 0,
                },
                _ => false
            },
        fail _ => false
    }

/// A `#[terminating]`-attributed def -- the same real corpus shape as
/// `std/map.mo`'s own `#[terminating] def insert ...` -- must still
/// parse correctly and carry the real attribute now, not just tolerate
/// and discard it.
#[test]
def test_def_parser_captures_terminating_attribute : Bool :=
    match def_parser "#[terminating]\ndef loop (x : I64) : I64 := loop x" {
        success rem out =>
            String.beq rem "" &&
            match out {
                Decl.def_d d => match d {
                    Def.mk _ _ _ _ attrs _ => has_attr (Identifier.id "terminating") attrs,
                },
                _ => false
            },
        fail _ => false
    }

#[test]
def test_type_parser_captures_derive_cli_attribute : Bool :=
    match type_parser "#[derive_cli]\ntype Command { help, }" {
        success rem out =>
            String.beq rem "" &&
            match out {
                Decl.inductive_d ind => match ind {
                    Inductive.mk _ _ _ _ attrs _ =>
                        I64.beq (List.length attrs) 1 && has_attr (Identifier.id "derive_cli") attrs,
                },
                _ => false
            },
        fail _ => false
    }

/// `#[derive BEq BOrd Debug Lens]` -- confirmed against the reference
/// grammar to be ONE attribute with four bare-ident args, not four
/// stacked attributes (see the Step 1 tests for `attribute_parser`
/// directly) -- must come through the same way once wired into
/// `type_parser`.
#[test]
def test_type_parser_captures_multi_arg_derive_attribute : Bool :=
    match type_parser "#[derive BEq BOrd]\ntype Point { mk (x : I64) (y : I64), }" {
        success rem out =>
            String.beq rem "" &&
            match out {
                Decl.inductive_d ind => match ind {
                    Inductive.mk _ _ _ _ attrs _ =>
                        I64.beq (List.length attrs) 1 &&
                        match attrs {
                            List.cons attr _ =>
                                match attr { Attribute.mk name args => id_eq name (Identifier.id "derive") && I64.beq (List.length args) 2 },
                            List.empty => false,
                        },
                },
                _ => false
            },
        fail _ => false
    }

/// A plain (unattributed) type must still parse with an empty attrs
/// list -- previously `type_parser` had no attribute tolerance AT ALL
/// (unlike `def_parser`, which at least skipped `#[...]`), so this
/// also confirms ordinary types are unaffected by adding it.
#[test]
def test_type_parser_no_attribute_present : Bool :=
    match type_parser "type Command { help, }" {
        success rem out =>
            String.beq rem "" &&
            match out {
                Decl.inductive_d ind => match ind {
                    Inductive.mk _ _ _ _ attrs _ => I64.beq (List.length attrs) 0,
                },
                _ => false
            },
        fail _ => false
    }

// --- Tests for quote_term_parser (Term.quote_) ---

#[test]
def test_quote_term_basic : Bool :=
    let empty_ctx : List Identifier := List.empty in
    match expression empty_ctx "quote { 1 }" {
        success rem out =>
            String.beq rem "" &&
            match out { Term.quote_ _inner => true, _ => false },
        fail _ => false
    }

/// The quoted body is a FULL, unrestricted term -- not a restricted
/// atom subset -- confirmed here with an application inside.
#[test]
def test_quote_term_application_body : Bool :=
    let f_id : Identifier := Identifier.id "f" in
    let ctx : List Identifier := List.cons f_id List.empty in
    match expression ctx "quote { f 1 }" {
        success rem out =>
            String.beq rem "" &&
            match out { Term.quote_ inner => match inner { Term.app _ _ => true, _ => false }, _ => false },
        fail _ => false
    }

/// Missing closing `}` must fail cleanly, not silently truncate.
#[test]
def test_quote_term_missing_close_fails : Bool :=
    let empty_ctx : List Identifier := List.empty in
    match expression empty_ctx "quote { 1" {
        success _ _ => false,
        fail _ => true
    }

/// `quote` used with no following `{` at all (e.g. mistyped/incomplete)
/// must fail cleanly rather than partially matching.
#[test]
def test_quote_term_no_brace_fails : Bool :=
    let empty_ctx : List Identifier := List.empty in
    match expression empty_ctx "quote 1" {
        success _ _ => false,
        fail _ => true
    }

// --- Tests for macro_call_term (Term.var_macro) ---

/// Demonstrates the raw ordering hazard `macro_call_term` being tried
/// BEFORE `variable` in `atom_parsers` fixes: `variable` on its own
/// happily matches just the identifier prefix of `foo!`, leaving `!`
/// unconsumed -- not a hypothetical failure mode, just something
/// `atom_parsers`' ordering now prevents from ever being reached.
#[test]
def test_variable_alone_would_misparse_macro_call_prefix : Bool :=
    let empty_ctx : List Identifier := List.empty in
    match variable empty_ctx "foo! 1" {
        success rem _ => not (String.beq rem ""),
        fail _ => false
    }

#[test]
def test_macro_call_term_basic : Bool :=
    let empty_ctx : List Identifier := List.empty in
    match expression empty_ctx "foo!" {
        success rem out =>
            String.beq rem "" &&
            match out {
                Term.var_macro _ dbg => match dbg {
                    DebugName.named id => id_eq id (Identifier.id "foo"),
                    DebugName.unnamed => false,
                },
                _ => false
            },
        fail _ => false
    }

/// `foo! 1 2` falls out of the ordinary atom-application machinery for
/// free once `foo!` parses as one atom -- no separate application-level
/// change was needed.
#[test]
def test_macro_call_term_with_args : Bool :=
    let empty_ctx : List Identifier := List.empty in
    match expression empty_ctx "foo! 1 2" {
        success rem out =>
            String.beq rem "" &&
            match out { Term.app _ _ => true, _ => false },
        fail _ => false
    }

/// A plain identifier with no `!` must still resolve to an ordinary
/// `Term.var`, not `Term.var_macro` -- confirms `macro_call_term`
/// being tried first doesn't change behavior for the common case.
#[test]
def test_macro_call_term_absent_falls_through_to_variable : Bool :=
    let x_id : Identifier := Identifier.id "x" in
    let ctx : List Identifier := List.cons x_id List.empty in
    match expression ctx "x" {
        success rem out =>
            String.beq rem "" &&
            match out { Term.var _ _ => true, _ => false },
        fail _ => false
    }

// --- Tests for defmacro (both forms) ---

/// Form B: `defmacro name params := <term>` -> `Decl.def_macro_d`, a
/// reused `Def` with `typ = Term.hole` and `term` wrapped in one lambda
/// per param.
#[test]
def test_defmacro_term_body_basic : Bool :=
    match decl_parser "defmacro double x := x" {
        success rem out =>
            String.beq rem "" &&
            match out {
                Decl.def_macro_d d => match d {
                    Def.mk _ typ term _ _ _ =>
                        (match typ { Term.hole => true, _ => false }) &&
                        (match term { Term.lam _ _ _ => true, _ => false }),
                },
                _ => false
            },
        fail _ => false
    }

/// A macro with no params at all -- `lam_params []` is identity, so the
/// body term is stored bare, no lambda wrapping.
#[test]
def test_defmacro_term_body_no_params : Bool :=
    match decl_parser "defmacro answer := 42" {
        success rem out =>
            String.beq rem "" &&
            match out {
                Decl.def_macro_d d => match d {
                    Def.mk _ _ term _ _ _ => match term { Term.lit _ => true, _ => false },
                },
                _ => false
            },
        fail _ => false
    }

/// Real bug found this round (macro-expansion phase, prerequisite fix
/// B): `defmacro`/`decl_list` were missing from `kw_list`
/// (lang/parser/core.mo), so `identifier` happily accepted either as
/// an ordinary variable name -- meaning a PRECEDING decl's own
/// expression parsing could silently swallow a following `defmacro`
/// declaration's whole keyword+name+params as juxtaposed-application
/// arguments (`def foo : I64 := 1` followed by `defmacro derive_lens T
/// := decls {...}` parsed `1 defmacro derive_lens T` as one
/// application chain, leaving the parser stranded right at `:=` with
/// no valid decl to match — "unknown declaration"). This is exactly
/// the real corpus shape `std/derive.mo`'s own `defmacro derive_lens T
/// := decls { reflect_type_info! T derive_lens_meta }` hit (confirmed
/// via `decls_parser_strict` directly failing on this two-decl shape
/// before the fix, succeeding after). A single standalone `defmacro`
/// decl (this file's other defmacro tests, all of which parse it as
/// the FIRST/only decl) never exercised this, which is why it went
/// undetected until a real multi-decl file surfaced it.
#[test]
def test_defmacro_not_swallowed_by_preceding_decl : Bool :=
    match decls_parser_strict "def foo : I64 := 1\n\ndefmacro derive_lens T := decls {\n    reflect_type_info! T derive_lens_meta\n}\n" {
        success rem decl_list =>
            String.beq rem "" &&
            I64.beq (List.length decl_list) 2 &&
            match decl_list {
                List.cons _ rest =>
                    match rest {
                        List.cons d2 _ => match d2 { Decl.decl_gen_d _ _ _ _ => true, _ => false },
                        List.empty => false,
                    },
                List.empty => false,
            },
        fail _ => false
    }

/// Form A: `defmacro name params := decls { ... }` -> `Decl.decl_gen_d`,
/// storing the literal (unexpanded) list of decl_list parsed out of the
/// body -- the real corpus shape (`std/derive.mo`'s own `defmacro
/// derive_lens T := decls { ... }`).
#[test]
def test_defmacro_decls_block_basic : Bool :=
    match decl_parser "defmacro make_getter T := decls { def get_it (x : T) : T := x }" {
        success rem out =>
            String.beq rem "" &&
            match out {
                Decl.decl_gen_d name params decl_list _attrs =>
                    id_eq (Identifier.id "make_getter") (module_path_last name) &&
                    I64.beq (List.length params) 1 &&
                    I64.beq (List.length decl_list) 1,
                _ => false
            },
        fail _ => false
    }

/// The real corpus shape one level deeper: a `decls { ... }` body that
/// itself contains a NESTED decl-position macro call (`std/derive.mo`'s
/// own `defmacro derive_lens T := decls { reflect_type_info! T
/// derive_lens_meta }`) -- confirms `decls_skip`'s reuse handles this
/// (needs the full `decl_parsers` alternation, including
/// `macro_call_decl_parser` itself, inside the nested block).
#[test]
def test_defmacro_decls_block_with_nested_macro_call : Bool :=
    match decl_parser "defmacro derive_lens T := decls { reflect_type_info! T derive_lens_meta }" {
        success rem out =>
            String.beq rem "" &&
            match out {
                Decl.decl_gen_d _ _ decl_list _attrs =>
                    match decl_list {
                        List.cons d _ => match d { Decl.macro_call_d name _ => id_eq name (Identifier.id "reflect_type_info"), _ => false },
                        List.empty => false,
                    },
                _ => false
            },
        fail _ => false
    }

#[partial]
def module_path_last (mp : ModulePath) : Identifier :=
    match mp { ModulePath.mp ids => list_last_or_default ids (Identifier.id "") }

#[partial]
def list_last_or_default (ids : List Identifier) (default_ : Identifier) : Identifier :=
    match ids {
        List.empty => default_,
        List.cons hd rest => match rest { List.empty => hd, List.cons _ _ => list_last_or_default rest default_ },
    }

// --- Tests for decl-position `name! args...` (Decl.macro_call_d), standalone ---

#[test]
def test_macro_call_decl_standalone_no_args : Bool :=
    match decl_parser "foo!" {
        success rem out =>
            String.beq rem "" &&
            match out { Decl.macro_call_d name args => id_eq name (Identifier.id "foo") && I64.beq (List.length args) 0, _ => false },
        fail _ => false
    }

#[test]
def test_macro_call_decl_standalone_with_args : Bool :=
    match decl_parser "reflect_type_info! T derive_lens_meta" {
        success rem out =>
            String.beq rem "" &&
            match out { Decl.macro_call_d name args => id_eq name (Identifier.id "reflect_type_info") && I64.beq (List.length args) 2, _ => false },
        fail _ => false
    }

/// Two consecutive top-level macro calls: the SECOND call's own name
/// must not be swallowed as an extra whitespace-separated argument of
/// the first -- confirms `peek_not_macro_call`'s lookahead guard
/// actually works, not just that a single call parses. Uses
/// `decls_parser` (the module-level multi-decl loop) since a single
/// `decl_parser` call only ever returns one `Decl`.
#[test]
def test_macro_call_decl_two_consecutive_not_swallowed : Bool :=
    match decls_parser "derive_beq! Point\nderive_bord! Point" {
        success rem decl_list =>
            String.beq rem "" &&
            I64.beq (List.length decl_list) 2 &&
            match decl_list {
                List.cons d1 rest =>
                    (match d1 { Decl.macro_call_d n1 a1 => id_eq n1 (Identifier.id "derive_beq") && I64.beq (List.length a1) 1, _ => false }) &&
                    (match rest {
                        List.cons d2 _ => match d2 { Decl.macro_call_d n2 a2 => id_eq n2 (Identifier.id "derive_bord") && I64.beq (List.length a2) 1, _ => false },
                        List.empty => false,
                    }),
                List.empty => false,
            },
        fail _ => false
    }

// --- Tests for per-def-param #[arg] attribute capture ---
//
// Lower-confidence/lower-priority per the plan -- the real corpus
// #[arg] usage (lang/tests/cli_derive_tests.mo) is on a constructor
// field, not a `def` param, and is deliberately Rust-host-only. These
// are hand-written repros only.

#[test]
def test_def_param_captures_arg_attribute : Bool :=
    let empty_params : List Param := List.empty in
    match def_params_loop "(#[arg] verbose : Bool)" empty_params {
        success rem params =>
            String.beq rem "" &&
            match params {
                List.cons p _ => match p {
                    Param.mk _ _ _ _ attrs => I64.beq (List.length attrs) 1 && has_attr (Identifier.id "arg") attrs,
                },
                List.empty => false,
            },
        fail _ => false
    }

/// A plain (unattributed) `def` param must still parse with an empty
/// attrs list -- confirms adding the capture doesn't change ordinary
/// def-param parsing.
#[test]
def test_def_param_no_attribute_present : Bool :=
    match def_parser "def foo (x : I64) : I64 := x" {
        success rem out =>
            String.beq rem "" &&
            match out { Decl.def_d _ => true, _ => false },
        fail _ => false
    }

/// Multi-name group with `#[arg]` -- both names get the same captured
/// attrs (the documented, untested-by-real-corpus design choice).
#[test]
def test_def_param_multi_name_group_with_attribute : Bool :=
    match def_parser "def foo (#[arg] a b : Bool) : I64 := 1" {
        success rem out =>
            String.beq rem "" &&
            match out { Decl.def_d _ => true, _ => false },
        fail _ => false
    }

#[test]
def test_match_bound_var : Bool :=
    let x : Identifier := Identifier.id "x" in
    let ctx : List Identifier := List.cons x List.empty in
    match match_parser ctx "match x { none => 0 }" {
        success rem out =>
            match out {
                lit val =>
                    match val {
                        match_ scrutinee cases =>
                            String.beq rem "",
                        _ => false
                    },
                _ => false
            },
        fail _ => false
    }

// ─── Canonical decl parser smoke tests (Phase 8) ─────────────────────

#[partial]
def use_filter_is_bare (filter : UseFilter) : Bool :=
    match filter {
        UseFilter.use_bare => true,
        _ => false
    }

#[partial]
def open_filter_is_all (filter : OpenFilter) : Bool :=
    match filter {
        OpenFilter.open_all => true,
        _ => false
    }

#[test]
def test_use_parser : Bool :=
    match use_parser "use prelude" {
        success rem out =>
            match out {
                use_d path filter _pub => (String.beq rem "") && use_filter_is_bare filter,
                _ => false
            },
        fail _ => false
    }

#[test]
def test_open_parser : Bool :=
    match open_parser "open IO" {
        success rem out =>
            match out {
                open_d path filter => (String.beq rem "") && open_filter_is_all filter,
                _ => false
            },
        fail _ => false
    }

#[partial]
def use_item_is_glob (item : UseItem) : Bool :=
    match item {
        UseItem.use_glob => true,
        _ => false
    }

#[test]
def test_use_glob : Bool :=
    match use_parser "use io {*}" {
        success rem out =>
            match out {
                use_d path filter _pub =>
                    match filter {
                        UseFilter.use_items items =>
                            match items {
                                List.cons item rest => (List.is_empty rest) && (use_item_is_glob item),
                                _ => false
                            },
                        _ => false
                    },
                _ => false
            },
        fail _ => false
    }

#[test]
def test_use_empty_braces : Bool :=
    match use_parser "use io {}" {
        success rem out =>
            match out {
                use_d path filter _pub =>
                    match filter {
                        UseFilter.use_items items => List.is_empty items,
                        _ => false
                    },
                _ => false
            },
        fail _ => false
    }

#[test]
def test_use_nested_simple : Bool :=
    match use_parser "use io {file {read}}" {
        success rem out =>
            match out {
                use_d path filter _pub =>
                    match filter {
                        UseFilter.use_items items =>
                            match items {
                                List.cons item rest =>
                                    match item {
                                        UseItem.use_sub name sub_items =>
                                            match sub_items {
                                                List.cons inner sub_rest =>
                                                    match inner {
                                                        UseItem.use_name inner_name =>
                                                            (List.is_empty rest) && (List.is_empty sub_rest)
                                                                && (String.beq (show_identifier name) "file") && (String.beq (show_identifier inner_name) "read"),
                                                        _ => false
                                                    },
                                                _ => false
                                            },
                                        _ => false
                                    },
                                _ => false
                            },
                        _ => false
                    },
                _ => false
            },
        fail _ => false
    }

#[test]
def test_use_nested_rename : Bool :=
    match use_parser "use io {file as f {read}}" {
        success rem out =>
            match out {
                use_d path filter _pub =>
                    match filter {
                        UseFilter.use_items items =>
                            match items {
                                List.cons item rest =>
                                    match item {
                                        UseItem.use_sub_rename name alias sub_items =>
                                            (List.is_empty rest) && (String.beq (show_identifier name) "file") && (String.beq (show_identifier alias) "f"),
                                        _ => false
                                    },
                                _ => false
                            },
                        _ => false
                    },
                _ => false
            },
        fail _ => false
    }

#[test]
def test_use_nested_deep : Bool :=
    match use_parser "use io {a {b {c}}}" {
        success rem out => String.beq rem "",
        fail _ => false
    }

#[test]
def test_use_multiple_rename : Bool :=
    match use_parser "use io {read as r, write as w}" {
        success rem out =>
            match out {
                use_d path filter _pub =>
                    match filter {
                        UseFilter.use_items items =>
                            match items {
                                List.cons a rest =>
                                    match rest {
                                        List.cons b rest2 => List.is_empty rest2,
                                        _ => false
                                    },
                                _ => false
                            },
                        _ => false
                    },
                _ => false
            },
        fail _ => false
    }

#[test]
def test_open_brace_filter : Bool :=
    match open_parser "open io {println}" {
        success rem out =>
            match out {
                open_d path filter =>
                    match filter {
                        OpenFilter.open_only names =>
                            match names {
                                List.cons name rest => (List.is_empty rest) && (String.beq (show_identifier name) "println"),
                                _ => false
                            },
                        _ => false
                    },
                _ => false
            },
        fail _ => false
    }

#[test]
def test_scoped_open_def : Bool :=
    match open_parser "open io in def main : IO Unit := println \"hi\"" {
        success rem out =>
            match out {
                scoped_open_d path filter decl =>
                    match decl {
                        def_d _ => open_filter_is_all filter,
                        _ => false
                    },
                _ => false
            },
        fail _ => false
    }

#[test]
def test_scoped_open_filtered : Bool :=
    match open_parser "open io {println} in def main : IO Unit := println \"hi\"" {
        success rem out =>
            match out {
                scoped_open_d path filter decl =>
                    match decl {
                        def_d _ =>
                            match filter {
                                OpenFilter.open_only _ => true,
                                _ => false
                            },
                        _ => false
                    },
                _ => false
            },
        fail _ => false
    }

#[test]
def test_infix_parser : Bool :=
    match infix_parser "infix (++) := List.append" {
        success rem out =>
            match out {
                infix_d op path _vis => String.beq rem "",
                _ => false
            },
        fail _ => false
    }

#[test]
def test_infix_parser_with_precedence : Bool :=
    match infix_parser "infix:5 (++) := List.append" {
        success rem out =>
            match out {
                infix_d op path _vis => String.beq rem "",
                _ => false
            },
        fail _ => false
    }

#[test]
def test_struct_parser : Bool :=
    match struct_parser "struct Point { x : I64, y : I64 }" {
        success rem out =>
            match out {
                struct_d s => String.beq rem "",
                _ => false
            },
        fail _ => false
    }

/// Regression test for struct field multiplicity markers
/// (`instance_implicit_params_loop`'s sibling feature for structs — see
/// `multiplicity_prefix`'s doc comment). `!data` should parse as Linear
/// while the unmarked `size` field defaults to Many.
#[test]
def test_struct_linear_field : Bool :=
    match struct_parser "struct Buffer { !data : String, size : I64 }" {
        success rem out =>
            String.beq rem "" && (match out {
                struct_d s => struct_first_field_is_linear s,
                _ => false
            }),
        fail _ => false
    }

#[partial]
def struct_first_field_is_linear (s : Struct) : Bool :=
    match s {
        Struct.mk _name fields _vis =>
            match fields {
                List.cons f rest => field_mult_is_linear f && field_mult_is_many_second rest,
                List.empty => false
            }
    }

#[partial]
def field_mult_is_linear (f : StructField) : Bool :=
    match f {
        StructField.mk _name _typ _default mult =>
            match mult {
                Multiplicity.linear => true,
                _ => false
            }
    }

#[partial]
def field_mult_is_many_second (fields : List StructField) : Bool :=
    match fields {
        List.cons f _rest =>
            match f {
                StructField.mk _name _typ _default mult =>
                    match mult {
                        Multiplicity.many => true,
                        _ => false
                    }
            },
        List.empty => false
    }

#[test]
def test_def_parser : Bool :=
    match def_parser "#[test] def f (x : I64) : I64 := x" {
        success rem out =>
            match out {
                def_d d => String.beq rem "",
                _ => false
            },
        fail _ => false
    }

/// Regression test for `def_try_constraints`: a `[Constraint, ...]`
/// clause between a def's name and its params — real usage:
/// `std/map.mo`'s `def BTreeMap.beq [BEq K, BEq V] (a b : BTreeMap K V)
/// : Bool := ...`, previously unparseable (`class`/`instance`/`type`
/// all already supported their own `[...]` clause, `def` never did).
/// Checks the constraints actually reach the parsed `Def`, not just
/// that the clause parses without error (`class`'s own equivalent bug
/// — see `class_apply_constraints`'s doc comment — hid behind
/// success-only tests for a long time).
#[test]
def test_def_parser_with_constraints : Bool :=
    match def_parser "def eq [BEq A] (a b : A) : Bool := true" {
        success rem out =>
            String.beq rem "" && (match out {
                def_d d => def_has_one_beq_a_constraint d,
                _ => false
            }),
        fail _ => false
    }

#[partial]
def def_has_one_beq_a_constraint (d : Def) : Bool :=
    match d {
        Def.mk _name _typ _term constraints _attrs _vis =>
            match constraints {
                List.cons tc rest => constraint_is_beq_a tc && list_is_empty_tc rest,
                List.empty => false
            }
    }

#[partial]
def constraint_is_beq_a (tc : TypeConstraint) : Bool :=
    match tc {
        TypeConstraint.mk cls vars =>
            Similar.similar cls (ModulePath.mp (List.cons (Identifier.id "BEq") List.empty))
                && (match vars {
                    List.cons v _ => Similar.similar v (Identifier.id "A"),
                    List.empty => false
                })
    }

/// The self-hosted parser couldn't previously re-parse its own source:
/// `lang/elaborate.mo`'s `def sentinel : I64 := -1` (unparenthesized
/// negative literal body) is real, live corpus content, not a
/// hypothetical.
#[test]
def test_def_parser_negative_body : Bool :=
    match def_parser "def sentinel : I64 := -1" {
        success rem out =>
            String.beq rem "" && (match out {
                def_d _ => true,
                _ => false
            }),
        fail _ => false
    }

// --- string_parse escape sequence tests ---
//
// Regression tests for `lang/parser/string.mo`'s escape handling: the
// previous version (`take_while is_not_quote`) stopped at the *first*
// raw `"` regardless of whether it was escaped, so any escaped quote
// truncated the string early instead of failing outright — invisible
// to a success/fail-only test, hence checking the decoded *content*
// below, not just parse success.

#[test]
def test_string_parse_plain : Bool :=
	match string_parse "\"hello\"" {
		success rem out => String.beq rem "" && term_lit_str_eq out "hello",
		fail _ => false
	}

#[test]
def test_string_parse_escaped_quote : Bool :=
	match string_parse "\"a\\\"b\"" {
		success rem out => String.beq rem "" && term_lit_str_eq out "a\"b",
		fail _ => false
	}

/// The specific ambiguity `string_body_escape`'s doc comment calls out:
/// an escaped backslash immediately followed by the REAL closing quote
/// must not be misread as "the quote is escaped too".
#[test]
def test_string_parse_escaped_backslash_before_close : Bool :=
	match string_parse "\"a\\\\\"" {
		success rem out => String.beq rem "" && term_lit_str_eq out "a\\",
		fail _ => false
	}

/// The exact corpus case that motivated this fix: `lang/json.mo`'s own
/// test fixture string, containing escaped quotes, backslash-n, and
/// backslash-t all in one literal.
#[test]
def test_string_parse_json_fixture : Bool :=
	match string_parse "\"\\\"a\\\\nb\\\\tc\\\\\\\"d\\\"\"" {
		success rem out => String.beq rem "" && term_lit_str_eq out "\"a\\nb\\tc\\\"d\"",
		fail _ => false
	}

#[test]
def test_string_parse_unknown_escape_fails : Bool :=
	match string_parse "\"a\\qb\"" {
		success _ _ => false,
		fail _ => true
	}

#[partial]
def term_lit_str_eq (t : Term) (expected : String) : Bool :=
	match t {
		Term.lit lit_val => match lit_val {
			Literal.str s => String.beq s expected,
			_ => false
		},
		_ => false
	}

#[test]
def test_def_do_block : Bool :=
    match def_parser "def main : Unit { return 0 }" {
        success rem out =>
            match out {
                def_d d => String.beq rem "",
                _ => false
            },
        fail _ => false
    }

#[test]
def test_class_parser : Bool :=
    match class_parser "class Show A { def show (a : A) : String }" {
        success rem out =>
            match out {
                class_d c => String.beq rem "",
                _ => false
            },
        fail _ => false
    }

#[test]
def test_instance_parser : Bool :=
    match instance_parser "instance Functor Maybe { def map f m := match m { some a => a, none => none } }" {
        success rem out =>
            match out {
                instance_d i => String.beq rem "",
                _ => false
            },
        fail _ => false
    }

#[test]
def test_decl_parser_def : Bool :=
    match decl_parser "def add (a: I64) (b: I64) : I64 := a + b" {
        success rem out =>
            match out {
                def_d d => String.beq rem "",
                _ => false
            },
        fail _ => false
    }

#[test]
def test_decl_parser_fail : Bool :=
    match decl_parser "foobar" {
        success rem out => false,
        fail _ => true
    }

/// End-to-end confirmation of the furthest-failure-wins fix
/// (`lang/parser/combinators.mo`'s `alt_fold`/`furthest_error`) plus
/// `decl_fail_to_unknown`'s relaxed relabeling: `def f (x` recognizes
/// the `def` keyword and gets partway into its parameter list before
/// failing on the missing `)` — that failure position is strictly
/// deeper into the input than `decl_parser`'s own starting point, so
/// it must survive as-is rather than being flattened to the generic
/// "unknown declaration" fallback (which is reserved for input that
/// doesn't match the start of any known declaration form at all, see
/// `test_decl_parser_fail` above).
#[test]
def test_decl_parser_preserves_deep_failure_position : Bool :=
    let source : String := "def f (x" in
    match decl_parser source {
        success _ _ => false,
        fail e => Bool.not (I64.beq (String.length (parse_error_remaining e)) (String.length source))
    }

// ─── AST debug helpers ───────────────────────────────────────────────────

#[partial]
def debug_decl_kind (d : Decl) : String :=
    match d {
        use_d _ _ => "use_d",
        open_d _ _ => "open_d",
        scoped_open_d _ _ _ => "scoped_open_d",
        def_d _ => "def_d",
        inductive_d _ => "inductive_d",
        infix_d _ _ => "infix_d",
        struct_d _ => "struct_d",
        class_d _ => "class_d",
        instance_d _ => "instance_d"
    }

#[partial]
def debug_decl_count (decl_list : List Decl) : I64 :=
    match decl_list {
        List.empty => 0,
        List.cons d rest => 1 + debug_decl_count rest
    }

// ─── Multi-declaration parser tests ──────────────────────────────────────────────────────

#[test]
def test_decls_empty : Bool :=
    match decls_parser "" {
        success rem decl_list =>
            String.beq rem "" && match decl_list {
                List.empty => true,
                List.cons _ _ => false
            },
        fail _ => false
    }

#[test]
def test_decls_whitespace_only : Bool :=
    match decls_parser "  " {
        success rem decl_list =>
            String.beq rem "" && match decl_list {
                List.empty => true,
                List.cons _ _ => false
            },
        fail _ => false
    }

#[test]
def test_decls_one_use : Bool :=
    match decls_parser "use prelude" {
        success rem decl_list => String.beq rem "",
        fail _ => false
    }

#[test]
def test_decls_two_parsed : Bool :=
    match decls_parser "use prelude open IO" {
        success rem decl_list => String.beq rem "",
        fail _ => false
    }

#[test]
def test_decls_def : Bool :=
    match decls_parser "def x : I64 := 42" {
        success rem decl_list => String.beq rem "",
        fail _ => false
    }

#[test]
def test_decls_decl_plus_noise : Bool :=
    match decls_parser "use prelude  garbage" {
        success rem decl_list => true,
        fail _ => false
    }

/// `decls_parser_strict`'s whole reason for existing: unlike the lenient
/// `decls_parser` (whose `test_decls_decl_plus_noise` above passes by
/// SILENTLY DISCARDING "garbage"), the strict twin correctly reports a
/// real failure — this is genuinely-broken content, not end-of-file.
#[test]
def test_decls_parser_strict_reports_failure_on_garbage : Bool :=
    match decls_parser_strict "use prelude  garbage" {
        success _ _ => false,
        fail _ => true
    }

/// On genuinely-complete, fully-parseable input, the strict and lenient
/// parsers agree.
#[test]
def test_decls_parser_strict_succeeds_on_clean_input : Bool :=
    match decls_parser_strict "use prelude open IO" {
        success rem decl_list => String.beq rem "" && I64.beq (debug_decl_count decl_list) 2,
        fail _ => false
    }

/// The rendered diagnostic for a real strict-mode failure round-trips
/// through `location_of_remaining`/`render_parse_error` end to end,
/// with the correct message and position — this is the exact shape
/// `lang.module`'s `try_parse_decls_strict` (and, through it,
/// `lang/main.mo`'s CLI error path) reports on a genuine parse failure.
#[test]
def test_decls_parser_strict_error_renders_with_position : Bool :=
    let source : String := "use prelude\n\ngarbage here" in
    match decls_parser_strict source {
        success _ _ => false,
        fail e =>
            let rendered : String := render_parse_error source Option.none e in
            string_contains_helper rendered "at 3:1" && string_contains_helper rendered "garbage here"
    }

#[partial]
def string_contains_helper (haystack : String) (needle : String) : Bool :=
    if I64.gt (String.length needle) (String.length haystack)
    then false
    else if String.beq (String.slice haystack 0 (String.length needle)) needle
    then true
    else if String.is_empty haystack
    then false
    else string_contains_helper (String.drop 1 haystack) needle

#[test]
def test_decls_count_two : Bool :=
    match decls_parser "use prelude open IO" {
        success rem decl_list =>
            String.beq rem "" && I64.beq (debug_decl_count decl_list) 2,
        fail _ => false
    }

#[test]
def test_decls_count_one : Bool :=
    match decls_parser "def x : I64 := 1" {
        success rem decl_list =>
            String.beq rem "" && I64.beq (debug_decl_count decl_list) 1,
        fail _ => false
    }

#[test]
def test_decls_kind_use : Bool :=
    match decls_parser "use prelude" {
        success rem decl_list =>
            match decl_list {
                List.cons d rest =>
                    match rest { List.empty => String.beq rem "", List.cons _ _ => false },
                List.empty => false
            },
        fail _ => false
    }

#[test]
def test_decls_type_decl : Bool :=
    match decls_parser "type Maybe A { some (a : A), none }" {
        success rem decl_list => String.beq rem "",
        fail _ => false
    }

// test_decls_class/test_decls_struct removed: identical input strings to
// test_class_parser/test_struct_parser above, just routed through
// decls_parser's dispatch instead of the direct parser, with a strictly
// weaker assertion (no Decl-variant match). decls_parser's dispatch
// mechanism (alt_fold over decl_parsers) is generic, not per-construct, and
// is already exercised for other decl kinds by test_decls_mixed below.

#[test]
def test_decls_mixed : Bool :=
    match decls_parser "use prelude  open IO  def main : I64 := 42" {
        success rem decl_list =>
            String.beq rem "" && I64.beq (debug_decl_count decl_list) 3,
        fail _ => false
    }

// ─── Phase 1.5 integration tests ───────────────────────────────────────────

// test_decls_fromlist_one_line removed: byte-for-byte identical input to
// test_class_with_default_param above, same class_parser call, strictly
// weaker assertion (just `true` on success, not even `rem == ""`).

#[test]
def test_decls_prelude_features : Bool :=
    match decls_parser "\ntype Any {\n  any {A : Type} (value: A)\n}\n\nclass Functor (F: Type -> Type) {\n  def map (f: A -> B) : (F A) -> F B\n}\n\nclass FromListLiteral (L : Type -> Type := List) {\n  def cons (a : A) : L A -> L A\n  def empty : L A\n}\n\n/// HAdd\nclass [HAdd A A] Add A {\n  def add (a: A) (b: A) : A\n}\n\ninstance [Show A] Show (List A) {\n  def show xs := \"list\"\n}\n" {
        success rem decl_list =>
            I64.beq (debug_decl_count decl_list) 5,
        fail _ => false
    }

#[test]
def test_decls_fromlist_one_line_nl : Bool :=
    match class_parser "class FromListLiteral (L : Type -> Type := List) {\n  def cons (a : A) : L A -> L A\n}\n" {
        success rem _ => true,
        fail _ => false
    }

#[test]
def test_decls_fromlist_empty_sig_nl : Bool :=
    match class_parser "class FromListLiteral (L : Type -> Type := List) {\n  def empty : L A\n}\n" {
        success rem _ => true,
        fail _ => false
    }

#[test]
def test_is_space_newline : Bool :=
  is_space "\n"
