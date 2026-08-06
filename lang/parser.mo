/// Self-hosted Monad grammar parser.
/// Split into modules for maintainability.
use lang.types
use std.list
use lang.parser.core
use lang.parser.char_preds
use lang.parser.combinators
use lang.parser.number
use lang.parser.whitespace
use lang.parser.position
use lang.parser.identifier
use lang.parser.string
open lang.parser.core
open ParseResult

@[partial]
def at_least_two (ids : List String) : Bool :=
	Bool.not (List.is_empty (List.tail ids))

def dotted_identifier (input : String) : ParseResult (List String) :=
	separated_by (tag ".") identifier input

/// Join a list of identifiers into a dotted string (e.g., ["Unit", "unit"] -> "Unit.unit")
@[partial]
def join_dotted_identifiers (ids : List String) : String := match ids {
    List.empty => "",
    List.cons hd rest => join_dotted_rest hd rest,
}

@[partial]
def join_dotted_rest (hd : String) (rest : List String) : String := match rest {
    List.empty => hd,
    List.cons x y => String.concat (String.concat hd ".") (join_dotted_identifiers rest),
}

/// Extract the identifier string from a NameRef
@[partial]
def name_ref_to_string (nref : NameRef) : Option String := match nref {
    NameRef.nid id => Option.some (show_identifier id),
    NameRef.nmp mp => Option.some (module_path_to_string mp),
    NameRef.nop op => Option.some (show_operator op),
}

/// Convert a ModulePath to a dotted string
@[partial]
def module_path_to_string (mp : ModulePath) : String := match mp {
    ModulePath.mp ids => join_dotted_identifiers (map_show_identifier ids),
}

/// Map a list of Identifiers to their string representations
@[partial]
def map_show_identifier (ids : List Identifier) : List String := match ids {
    List.empty => List.empty,
    List.cons hd rest => List.cons (show_identifier hd) (map_show_identifier rest),
}

/// Show an Identifier as a string
@[partial]
def show_identifier (id : Identifier) : String := match id {
    Identifier.id s => s,
}

/// Show an Operator as a string
@[partial]
def show_operator (op : Operator) : String := match op {
    Operator.operator s => s,
}

/// Find the last occurrence of a substring in a string, return its index or -1
@[partial]
def string_find_last (haystack : String) (needle : String) : I64 :=
    if String.beq needle "" then -1
    else if I64.gt (String.length needle) (String.length haystack) then -1
    else string_find_last_loop haystack needle (String.length haystack - String.length needle)

@[partial]
def string_find_last_loop (haystack : String) (needle : String) (start_idx : I64) : I64 :=
    if I64.lt start_idx 0 then -1
    else if String.beq (String.slice haystack start_idx (start_idx + String.length needle)) needle then start_idx
    else string_find_last_loop haystack needle (start_idx - 1)

@[partial]
def path_variable (input : String) : ParseResult TermV0 :=
        match dotted_identifier input {
                success rem ids =>
                        if at_least_two ids
                        then success rem (TermV0.var (NameRef.nmp (ModulePath.mp (List.map Identifier.id ids))))
                        else fail (ParseError.custom "not a dotted path"),
                fail e => fail e
        }

@[partial]
def do_stmts_tail (input : String) : String :=
	do_stmts_tail_sp (take_while is_space input) input

@[partial]
def do_stmts_tail_sp (r : ParseResult String) (orig : String) : String :=
	match r {
		success rem _ => do_stmts_tail_semi (tag ";" rem) rem orig,
		fail _ => orig
	}

@[partial]
def do_stmts_tail_semi (r : ParseResult String) (after_sp : String) (orig : String) : String :=
	match r {
		success rem _ => skip_spaces rem,
		fail _ => after_sp
	}

@[partial]
def do_stmt_return (ctx: List Identifier) (input: String) : ParseResult DoStmt :=
    do_stmt_ret_kw (tag "return" input) input ctx

@[partial]
def do_stmt_ret_kw (r: ParseResult String) (orig: String) (ctx: List Identifier) : ParseResult DoStmt :=
    match r {
        success rem _ => do_stmt_ret_expr (expression ctx (skip_spaces rem)),
        fail _ => do_stmt_try_let (tag "let" (skip_spaces orig)) orig ctx
    }

@[partial]
def do_stmt_ret_expr (r: ParseResult Term) : ParseResult DoStmt :=
    match r {
        success rem value => success rem (DoStmt.ret_s value),
        fail e => fail e
    }

@[partial]
def do_stmt_try_let (r: ParseResult String) (orig: String) (ctx: List Identifier) : ParseResult DoStmt :=
    match r {
        success rem _ => do_stmt_let_name (identifier (skip_spaces rem)) ctx,
        fail _ => do_stmt_expr (expression ctx (skip_spaces orig))
    }

@[partial]
def do_stmt_let_name (r: ParseResult String) (ctx: List Identifier) : ParseResult DoStmt :=
    match r {
        success rem name => do_stmt_let_kind rem (Identifier.id name) ctx,
        fail e => fail e
    }

@[partial]
def do_stmt_let_kind (input: String) (name: Identifier) (ctx: List Identifier) : ParseResult DoStmt :=
    do_stmt_let_kind_try (tag ":=" (skip_spaces input)) name input ctx

@[partial]
def do_stmt_let_kind_try (r: ParseResult String) (name: Identifier) (orig: String) (ctx: List Identifier) : ParseResult DoStmt :=
    match r {
        success rem _ => do_stmt_let_value (expression ctx (skip_spaces rem)) name,
        fail _ => do_stmt_bind_arrow (tag "<-" (skip_spaces orig)) name orig ctx
    }

@[partial]
def do_stmt_let_value (r: ParseResult Term) (name: Identifier) : ParseResult DoStmt :=
    match r {
        success rem value => success rem (DoStmt.let_s name value),
        fail e => fail e
    }

@[partial]
def do_stmt_bind_arrow (r: ParseResult String) (name: Identifier) (orig: String) (ctx: List Identifier) : ParseResult DoStmt :=
    match r {
        success rem _ => do_stmt_bind_value (expression ctx (skip_spaces rem)) name,
        fail _ => fail (ParseError.custom "expected := or <- after let in do block")
    }

@[partial]
def do_stmt_bind_value (r: ParseResult Term) (name: Identifier) : ParseResult DoStmt :=
    match r {
        success rem value => success rem (DoStmt.bind_s name value),
        fail e => fail e
    }

@[partial]
def do_stmt_expr (r: ParseResult Term) : ParseResult DoStmt :=
    match r {
        success rem value => success rem (DoStmt.expr_s value),
        fail e => fail e
    }

@[partial]
def do_stmts_extend_ctx (stmt: DoStmt) (ctx: List Identifier) : List Identifier :=
    match stmt {
        bind_s name _ => List.cons name ctx,
        let_s name _ => List.cons name ctx,
        _ => ctx
    }

@[partial]
def do_stmts (ctx: List Identifier) (input: String) : ParseResult (List DoStmt) :=
    do_stmts_check_end (tag "}" (skip_spaces input)) input ctx

@[partial]
def do_stmts_check_end (r: ParseResult String) (orig: String) (ctx: List Identifier) : ParseResult (List DoStmt) :=
    match r {
        success rem _ =>
            let empty : List DoStmt := List.empty in
            success rem empty,
        fail _ => do_stmts_first (do_stmt_return ctx (skip_spaces orig)) (skip_spaces orig) ctx
    }

@[partial]
def do_stmts_first (r: ParseResult DoStmt) (orig: String) (ctx: List Identifier) : ParseResult (List DoStmt) :=
    match r {
        success rem stmt => do_stmts_next2 (do_stmts (do_stmts_extend_ctx stmt ctx) (do_stmts_tail rem)) stmt,
        fail e => fail e
    }

@[partial]
def do_stmts_next2 (r: ParseResult (List DoStmt)) (first: DoStmt) : ParseResult (List DoStmt) :=
    match r {
        success rem rest => success rem (List.cons first rest),
        fail e => fail e
    }

@[partial]
def do_parser (ctx: List Identifier) (input: String) : ParseResult Term :=
    do_parser_kw (tag "do" input) ctx

@[partial]
def do_parser_kw (r: ParseResult String) (ctx: List Identifier) : ParseResult Term :=
    match r {
        success rem _ => do_parser_open (tag "{" (skip_spaces rem)) ctx,
        fail e => fail e
    }

@[partial]
def do_parser_open (r: ParseResult String) (ctx: List Identifier) : ParseResult Term :=
    match r {
        success rem _ => do_parser_stmts (do_stmts ctx rem) ctx,
        fail e => fail e
    }

@[partial]
def do_parser_stmts (r: ParseResult (List DoStmt)) (ctx: List Identifier) : ParseResult Term :=
    match r {
        success rem stmts => do_parser_desugar rem stmts,
        fail e => fail e
    }

@[partial]
def do_parser_desugar (rem: String) (stmts: List DoStmt) : ParseResult Term :=
    success rem (desugar_do stmts)

@[partial]
def is_newline (c : String) : Bool :=
	String.beq c "\n"

@[partial]
def is_not_newline (c : String) : Bool :=
	if String.beq c "\n" then false
	else true

@[partial]
def is_close_curly (c : String) : Bool :=
	String.beq c "}"

@[partial]
def is_not_close_curly (c : String) : Bool :=
	if String.beq c "}" then false
	else true

@[partial]
def is_not_close_paren (c : String) : Bool :=
	if String.beq c ")" then false
	else true

@[partial]
def is_op_char (c : String) : Bool :=
	op_char_member c op_chars

@[partial]
def op_check (s : String) (rem : String) : ParseResult String :=
	if is_empty s
	then fail (ParseError.custom "expected operator")
	else if I64.beq 0 (op_precedence s)
		then fail (ParseError.custom "unknown operator")
		else success rem s

@[partial]
def operator_parse (input : String) : ParseResult String :=
	bind_parse (take_while is_op_char) op_check input

@[partial]
def op_precedence (op : String) : I64 :=
	op_lookup_prec op op_table

@[partial]
def ids_to_module_path (ids : List String) : ModulePath :=
	ModulePath.mp (List.map Identifier.id ids)

@[partial]
def module_path_parser (input : String) : ParseResult ModulePath :=
	map_parse ids_to_module_path dotted_identifier input

// use module.path

@[partial]
def is_not_bracket (c : String) : Bool :=
	if String.beq "]" c then false
	else true

@[partial]
def is_not_attr_end (c : String) : Bool :=
	if String.beq "]" c then false
	else true

@[partial]
def lam_params (params : List Param) (body : Term) : Term :=
	let rev : List Param := list_reverse params in
	lam_params_loop rev body

@[partial]
def lam_params_loop (params : List Param) (body : Term) : Term :=
	match params {
		List.cons p rest =>
			match p {
				Param.mk name type_ mult default =>
					lam_params_loop rest (Term.lam (DebugName.named name) type_ body)
			},
		List.empty => body
	}

@[partial]
def def_to_decl (body : Term) (name : Identifier) (typ : Term) : Decl :=
	let empty_constraints : List TypeConstraint := List.empty in
	let empty_attrs : List String := List.empty in
	Decl.def_d (Def.mk (ModulePath.mp (List.cons name List.empty)) typ body empty_constraints empty_attrs)

// --- Canonical declaration parsers (de Bruijn Term) ---

// Helper: build de Bruijn binding context from param names (reversed = innermost first).

@[partial]
def ctx_of_params (params : List Param) : List Identifier :=
	let empty_ctx : List Identifier := List.empty in
	ctx_of_params_loop params empty_ctx

@[partial]
def ctx_of_params_loop (params : List Param) (acc : List Identifier) : List Identifier :=
	match params {
		List.cons p rest =>
			match p {
				Param.mk name type_ mult default =>
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

@[partial]
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

@[partial]
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

@[partial]
def use_brace_item_sub (input : String) : ParseResult UseItem :=
	match identifier input {
		success rem name => use_brace_item_sub_items name rem,
		fail e => fail e
	}

@[partial]
def use_brace_item_sub_items (name : String) (input : String) : ParseResult UseItem :=
	match use_brace_items (skip_spaces input) {
		success rem items => success rem (UseItem.use_sub (Identifier.id name) items),
		fail e => fail e
	}

@[partial]
def use_brace_item_sub_rename (input : String) : ParseResult UseItem :=
	match identifier input {
		success rem name => use_brace_item_sub_rename_alias name rem,
		fail e => fail e
	}

@[partial]
def use_brace_item_sub_rename_alias (name : String) (input : String) : ParseResult UseItem :=
	match as_kw (skip_spaces input) {
		success rem _ => match identifier (skip_spaces rem) {
			success rem2 alias => use_brace_item_sub_rename_items name alias rem2,
			fail e => fail e
		},
		fail e => fail e
	}

@[partial]
def use_brace_item_sub_rename_items (name : String) (alias : String) (input : String) : ParseResult UseItem :=
	match use_brace_items (skip_spaces input) {
		success rem items => success rem (UseItem.use_sub_rename (Identifier.id name) (Identifier.id alias) items),
		fail e => fail e
	}

@[partial]
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

@[partial]
def use_parser (input : String) : ParseResult Decl :=
	match tag "use" input {
		success rem _ => match module_path_parser (skip_spaces rem) {
			success rem2 path => use_after_path path rem2,
			fail e => fail e
		},
		fail e => fail e
	}

def use_after_path (path : ModulePath) (input : String) : ParseResult Decl :=
	match use_opt_filter input {
		success rem filter => success rem (Decl.use_d path filter),
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

@[partial]
def open_parser (input : String) : ParseResult Decl :=
	match tag "open" input {
		success rem _ => match module_path_parser (skip_spaces rem) {
			success rem2 path => open_after_path path rem2,
			fail e => fail e
		},
		fail e => fail e
	}

@[partial]
def open_after_path (path : ModulePath) (input : String) : ParseResult Decl :=
	match open_opt_filter input {
		success rem filter => open_after_filter path filter rem,
		fail e => fail e
	}

@[partial]
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
	match tag "infix" input {
		success rem _ => infix_after_kw rem,
		fail e => fail e
	}

def infix_precedence_clause (input : String) : ParseResult I64 :=
	preceded_by infix_colon_tag number input

def infix_colon_tag (input : String) : ParseResult String :=
	tag ":" (skip_spaces input)

def infix_after_kw (input : String) : ParseResult Decl :=
	match opt infix_precedence_clause input {
		success rem _ => infix_paren rem,
		fail e => fail e
	}

def infix_paren (input : String) : ParseResult Decl :=
	match tag "(" (skip_spaces input) {
		success rem _ => infix_op rem,
		fail e => fail e
	}

def infix_op (input : String) : ParseResult Decl :=
	match operator_parse (skip_spaces input) {
		success rem op => infix_close rem op,
		fail e => fail e
	}

def infix_close (input : String) (op : String) : ParseResult Decl :=
	match tag ")" (skip_spaces input) {
		success rem _ => infix_assign rem op,
		fail e => fail e
	}

def infix_assign (input : String) (op : String) : ParseResult Decl :=
	match tag ":=" (skip_spaces input) {
		success rem _ => infix_path rem op,
		fail e => fail e
	}

def infix_path (input : String) (op : String) : ParseResult Decl :=
	match module_path_parser (skip_spaces input) {
		success rem path => success rem (Decl.infix_d (Operator.operator op) path),
		fail e => fail e
	}

// struct Name { field1 : Type, field2 : Type := default }

@[partial]
def struct_parser (input : String) : ParseResult Decl :=
	struct_kw (tag "struct" input)

@[partial]
def struct_kw (r : ParseResult String) : ParseResult Decl :=
	match r {
		success rem _ => struct_name (identifier (skip_spaces rem)),
		fail e => fail e
	}

@[partial]
def struct_name (r : ParseResult String) : ParseResult Decl :=
	match r {
		success rem name => struct_brace (tag "{" (skip_spaces rem)) (Identifier.id name),
		fail e => fail e
	}

@[partial]
def struct_brace (r : ParseResult String) (name : Identifier) : ParseResult Decl :=
	match r {
		success rem _ => struct_fields rem name,
		fail e => fail e
	}

@[partial]
def struct_fields (input : String) (name : Identifier) : ParseResult Decl :=
	let empty_ctx : List Identifier := List.empty in
	match separated_by (tag ",") (preceded_by ws0 (struct_one_field empty_ctx)) input {
		success rem fields =>
			match tag "}" (skip_spaces rem) {
				success rem2 _ => success rem2 (Decl.struct_d (Struct.mk name fields)),
				fail e => fail (ParseError.custom "expected }")
			},
		fail e => fail e
	}

@[partial]
def struct_one_field (ctx : List Identifier) (input : String) : ParseResult StructField :=
	struct_field_name (identifier input) ctx

@[partial]
def struct_field_name (r : ParseResult String) (ctx : List Identifier) : ParseResult StructField :=
	match r {
		success rem name => struct_field_colon (tag ":" (skip_spaces rem)) (Identifier.id name) ctx,
		fail e => fail e
	}

@[partial]
def struct_field_colon (r : ParseResult String) (name : Identifier) (ctx : List Identifier) : ParseResult StructField :=
	match r {
		success rem _ => struct_field_type (type_expression ctx (skip_spaces rem)) name ctx,
		fail e => fail e
	}

@[partial]
def struct_field_type (r : ParseResult Term) (name : Identifier) (ctx : List Identifier) : ParseResult StructField :=
	match r {
		success rem typ => struct_field_default (tag ":=" (skip_spaces rem)) rem name typ ctx,
		fail e => fail e
	}

@[partial]
def struct_field_default (r : ParseResult String) (orig : String) (name : Identifier) (typ : Term) (ctx : List Identifier) : ParseResult StructField :=
	match r {
		success rem _ => struct_field_default_val (expression ctx (skip_spaces rem)) name typ,
		fail _ =>
			let none : Option Term := Option.none in
			success orig (StructField.mk name typ none)
	}

@[partial]
def struct_field_default_val (r : ParseResult Term) (name : Identifier) (typ : Term) : ParseResult StructField :=
	match r {
		success rem defval =>
			let some_val : Option Term := Option.some defval in
			success rem (StructField.mk name typ some_val),
		fail e => fail e
	}

// type Name { constructor1 (args), constructor2 }

@[partial]
def type_parser (input : String) : ParseResult Decl :=
	type_kw (tag "type" input)

@[partial]
def type_kw (r : ParseResult String) : ParseResult Decl :=
	match r {
		success rem _ => type_name (identifier (skip_spaces rem)),
		fail e => fail e
	}

@[partial]
def type_name (r : ParseResult String) : ParseResult Decl :=
	match r {
		success rem name =>
			let empty_params : List Identifier := List.empty in
			type_params_skip rem (Identifier.id name) empty_params,
		fail e => fail e
	}

@[partial]
def type_params_skip (input : String) (name : Identifier) (params : List Identifier) : ParseResult Decl :=
	type_params_skip_try (identifier (skip_spaces input)) input name params

@[partial]
def type_params_skip_try (r : ParseResult String) (orig : String) (name : Identifier) (params : List Identifier) : ParseResult Decl :=
	match r {
		success rem next => type_params_skip rem name (List.cons (Identifier.id next) params),
		fail _ => type_brace (tag "{" (skip_spaces orig)) name
	}

@[partial]
def type_brace (r : ParseResult String) (name : Identifier) : ParseResult Decl :=
	match r {
		success rem _ => type_constructors rem name,
		fail e => fail e
	}

@[partial]
def type_constructors (input : String) (name : Identifier) : ParseResult Decl :=
	let empty_ctx : List Identifier := List.empty in
	match separated_by (tag ",") (preceded_by ws0 (type_one_constructor empty_ctx)) input {
		success rem cons =>
			match tag "}" (skip_spaces rem) {
				success rem2 _ => success rem2 (type_to_decl name cons),
				fail e => fail (ParseError.custom "expected }")
			},
		fail e => fail e
	}

@[partial]
def type_one_constructor (ctx : List Identifier) (input : String) : ParseResult InductConstructor :=
	type_cons_name (identifier input) ctx

@[partial]
def type_cons_name (r : ParseResult String) (ctx : List Identifier) : ParseResult InductConstructor :=
	match r {
		success rem name => type_cons_paren_or_nil (tag "(" (skip_spaces rem)) rem (Identifier.id name) ctx,
		fail e => fail e
	}

@[partial]
def type_cons_paren_or_nil (r : ParseResult String) (orig : String) (name : Identifier) (ctx : List Identifier) : ParseResult InductConstructor :=
	match r {
		success rem _ => type_cons_params (type_param_list ctx rem) name,
		fail _ => type_cons_implicit (tag "{" (skip_spaces orig)) orig name ctx
	}

@[partial]
def type_cons_implicit (r : ParseResult String) (orig : String) (name : Identifier) (ctx : List Identifier) : ParseResult InductConstructor :=
	match r {
		success rem _ => type_cons_implicit_skip (take_while is_not_close_curly rem) rem orig name ctx,
		fail _ =>
			let empty_params : List Param := List.empty in
			success orig (InductConstructor.mk (ModulePath.mp (List.cons name List.empty)) empty_params (Term.hole))
	}

@[partial]
def type_cons_implicit_skip (r : ParseResult String) (rem : String) (orig : String) (name : Identifier) (ctx : List Identifier) : ParseResult InductConstructor :=
	match r {
		success after_bracket _ => type_cons_implicit_close (tag "}" (skip_spaces after_bracket)) after_bracket orig name ctx,
		fail _ =>
			let empty_params : List Param := List.empty in
			success orig (InductConstructor.mk (ModulePath.mp (List.cons name List.empty)) empty_params (Term.hole))
	}

@[partial]
def type_cons_implicit_close (r : ParseResult String) (after_bracket : String) (orig : String) (name : Identifier) (ctx : List Identifier) : ParseResult InductConstructor :=
	match r {
		success rem _ => type_cons_paren_or_nil (tag "(" (skip_spaces rem)) rem name ctx,
		fail _ =>
			let empty_params : List Param := List.empty in
			success after_bracket (InductConstructor.mk (ModulePath.mp (List.cons name List.empty)) empty_params (Term.hole))
	}

@[partial]
def type_cons_params (r : ParseResult (List Param)) (name : Identifier) : ParseResult InductConstructor :=
	match r {
		success rem params => type_cons_close_paren (tag ")" (skip_spaces rem)) name params,
		fail e => fail e
	}

@[partial]
def type_cons_close_paren (r : ParseResult String) (name : Identifier) (params : List Param) : ParseResult InductConstructor :=
	match r {
		success rem _ => success rem (InductConstructor.mk (ModulePath.mp (List.cons name List.empty)) params (Term.hole)),
		fail e => fail e
	}

@[partial]
def type_param_list (ctx : List Identifier) (input : String) : ParseResult (List Param) :=
	separated_by (tag ",") (preceded_by ws0 (type_one_param ctx)) input

@[partial]
def type_one_param (ctx : List Identifier) (input : String) : ParseResult Param :=
	type_one_param_name (identifier input) ctx

@[partial]
def type_one_param_name (r : ParseResult String) (ctx : List Identifier) : ParseResult Param :=
	match r {
		success rem name => type_one_param_type (tag ":" (skip_spaces rem)) (Identifier.id name) ctx,
		fail e => fail e
	}

@[partial]
def type_one_param_type (r : ParseResult String) (name : Identifier) (ctx : List Identifier) : ParseResult Param :=
	match r {
		success rem _ => type_one_param_val (type_expression ctx (skip_spaces rem)) name,
		fail e => fail e
	}

@[partial]
def type_one_param_val (r : ParseResult Term) (name : Identifier) : ParseResult Param :=
	match r {
		success rem typ => success rem (param_many name typ),
		fail e => fail e
	}

@[partial]
def type_to_decl (name : Identifier) (cons : List InductConstructor) : Decl :=
	let empty_params : List Param := List.empty in
	let empty_attrs : List String := List.empty in
	Decl.inductive_d (Inductive.mk (ModulePath.mp (List.cons name List.empty)) empty_params (Term.type_ 1) cons empty_attrs)

// def [#attrs] name {implicit} (explicit) : ret_type := body
// `#[...]` is the current attribute delimiter; `@[...]` is the deprecated
// predecessor (still parses, flagged by the bootstrap compiler). Content is
// skipped either way — see the module doc comment on attribute capture.

@[partial]
def def_parser (input : String) : ParseResult Decl :=
	def_try_attrs (alt_fold [tag "#[", tag "@["] (skip_spaces input)) input

@[partial]
def def_try_attrs (r : ParseResult String) (orig : String) : ParseResult Decl :=
	match r {
		success rem _ => def_attr_skip (take_while is_not_attr_end rem) rem,
		fail _ => def_kw (tag "def" (skip_spaces orig))
	}

@[partial]
def def_attr_skip (r : ParseResult String) (rest : String) : ParseResult Decl :=
	match r {
		success rem _ => def_attr_close (tag "]" rem),
		fail _ => fail (ParseError.custom "expected ]")
	}

@[partial]
def def_attr_close (r : ParseResult String) : ParseResult Decl :=
	match r {
		success rem _ => def_kw (tag "def" (skip_spaces rem)),
		fail e => fail e
	}

@[partial]
def def_kw (r : ParseResult String) : ParseResult Decl :=
	match r {
		success rem _ => def_name (identifier (skip_spaces rem)),
		fail e => fail e
	}

@[partial]
def def_name (r : ParseResult String) : ParseResult Decl :=
	match r {
		success rem name =>
			let empty : List Param := List.empty in
			def_params (def_params_loop (skip_spaces rem) empty) (Identifier.id name),
		fail e => fail e
	}

@[partial]
def def_params_loop (input : String) (params : List Param) : ParseResult (List Param) :=
	def_params_try_implicit (tag "{" input) input params

@[partial]
def def_params_try_implicit (r : ParseResult String) (orig : String) (params : List Param) : ParseResult (List Param) :=
	match r {
		success rem _ => def_implicit_param (identifier (skip_spaces rem)) rem params,
		fail _ => def_params_try_explicit (tag "(" orig) orig params
	}

@[partial]
def def_implicit_param (r : ParseResult String) (rem : String) (params : List Param) : ParseResult (List Param) :=
	match r {
		success rem2 name => def_implicit_colon (tag ":" (skip_spaces rem2)) rem rem2 name params,
		fail e => fail e
	}

@[partial]
def def_implicit_colon (r : ParseResult String) (brace_rem : String) (rem : String) (name : String) (params : List Param) : ParseResult (List Param) :=
	match r {
		success rem2 _ =>
			let empty_ctx : List Identifier := List.empty in
			def_implicit_type (type_expression empty_ctx rem2) brace_rem rem name params,
		fail e => fail e
	}

@[partial]
def def_implicit_type (r : ParseResult Term) (brace_rem : String) (rem : String) (name : String) (params : List Param) : ParseResult (List Param) :=
	match r {
		success rem2 typ => def_implicit_close (tag "}" rem2) brace_rem name typ params,
		fail e => fail e
	}

@[partial]
def def_implicit_close (r : ParseResult String) (brace_rem : String) (name : String) (typ : Term) (params : List Param) : ParseResult (List Param) :=
	match r {
		success rem2 _ =>
			let empty : List Param := List.empty in
			def_params_loop (skip_spaces rem2) empty,
		fail e => fail e
	}

@[partial]
def def_params_try_explicit (r : ParseResult String) (orig : String) (params : List Param) : ParseResult (List Param) :=
	match r {
		success rem _ => def_explicit_param (identifier (skip_spaces rem)) rem params,
		fail _ =>
			let rev : List Param := list_reverse params in
			success orig rev
	}

@[partial]
def def_explicit_param (r : ParseResult String) (close_rem : String) (params : List Param) : ParseResult (List Param) :=
	match r {
		success rem name => def_explicit_colon (tag ":" (skip_spaces rem)) close_rem name params,
		fail e => fail e
	}

@[partial]
def def_explicit_colon (r : ParseResult String) (close_rem : String) (name : String) (params : List Param) : ParseResult (List Param) :=
	match r {
		success rem _ =>
			let empty_ctx : List Identifier := List.empty in
			def_explicit_type (type_expression empty_ctx rem) close_rem name params,
		fail e => fail e
	}

@[partial]
def def_explicit_type (r : ParseResult Term) (close_rem : String) (name : String) (params : List Param) : ParseResult (List Param) :=
	match r {
		success rem typ => def_explicit_close (tag ")" rem) close_rem name typ params,
		fail e => fail e
	}

@[partial]
def def_explicit_close (r : ParseResult String) (close_rem : String) (name : String) (typ : Term) (params : List Param) : ParseResult (List Param) :=
	match r {
		success rem _ => def_params_loop (skip_spaces rem) (List.cons (param_many (Identifier.id name) typ) params),
		fail e => fail e
	}

@[partial]
def def_params (r : ParseResult (List Param)) (name : Identifier) : ParseResult Decl :=
	match r {
		success rem params => def_ret_type (tag ":" (skip_spaces rem)) rem name params,
		fail e => fail e
	}

@[partial]
def def_ret_type (r : ParseResult String) (orig : String) (name : Identifier) (params : List Param) : ParseResult Decl :=
	match r {
		success rem _ =>
			let empty_ctx : List Identifier := List.empty in
			def_ret_expr (type_expression empty_ctx rem) name params,
		fail _ => fail (ParseError.custom "expected : return type")
	}

@[partial]
def def_ret_expr (r : ParseResult Term) (name : Identifier) (params : List Param) : ParseResult Decl :=
	match r {
		success rem typ => def_body rem name params typ,
		fail e => fail e
	}

@[partial]
def def_body (input : String) (name : Identifier) (params : List Param) (typ : Term) : ParseResult Decl :=
	def_body_assign (tag ":=" (skip_spaces input)) name params typ input

@[partial]
def def_body_assign (r : ParseResult String) (name : Identifier) (params : List Param) (typ : Term) (orig : String) : ParseResult Decl :=
	match r {
		success rem _ => def_body_expr (expression (ctx_of_params params) (skip_spaces rem)) name params typ,
		fail _ => def_body_block_or_none (tag "{" (skip_spaces orig)) name params typ orig
	}

@[partial]
def def_body_block_or_none (r : ParseResult String) (name : Identifier) (params : List Param) (typ : Term) (orig : String) : ParseResult Decl :=
	match r {
		success rem _ => def_body_do (do_stmts (ctx_of_params params) rem) name params typ,
		fail _ => success orig (def_to_decl (lam_params params (Term.hole)) name typ)
	}

@[partial]
def def_body_expr (r : ParseResult Term) (name : Identifier) (params : List Param) (typ : Term) : ParseResult Decl :=
	match r {
		success rem body => success rem (def_to_decl (lam_params params body) name typ),
		fail e => fail e
	}

@[partial]
def def_body_block (r : ParseResult String) (name : Identifier) (params : List Param) (typ : Term) : ParseResult Decl :=
	match r {
		success rem _ => def_body_do (do_stmts (ctx_of_params params) rem) name params typ,
		fail e => fail e
	}

@[partial]
def def_body_do (r : ParseResult (List DoStmt)) (name : Identifier) (params : List Param) (typ : Term) : ParseResult Decl :=
	match r {
		success rem stmts => success rem (def_to_decl (lam_params params (desugar_do stmts)) name typ),
		fail e => fail e
	}

// ---------- TypeConstraint parser ----------

@[partial]
def type_constraint_one (input : String) : ParseResult TypeConstraint :=
	type_constraint_one_name (module_path_parser input) input

@[partial]
def type_constraint_one_name (r : ParseResult ModulePath) (orig : String) : ParseResult TypeConstraint :=
	match r {
		success rem cls =>
			let empty_vars : List Identifier := List.empty in
			type_constraint_vars (take_while is_ident_char (skip_spaces rem)) cls empty_vars rem,
		fail _ => fail (ParseError.custom "expected class name in constraint")
	}

@[partial]
def type_constraint_vars (r : ParseResult String) (cls : ModulePath) (acc : List Identifier) (orig : String) : ParseResult TypeConstraint :=
	match r {
		success rest ident =>
			if is_empty ident
			then success rest (TypeConstraint.mk cls (list_reverse acc))
			else type_constraint_vars (take_while is_ident_char (skip_spaces rest)) cls (List.cons (Identifier.id ident) acc) orig,
		fail _ => success orig (TypeConstraint.mk cls (list_reverse acc))
	}

@[partial]
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

@[partial]
def class_parser (input : String) : ParseResult Decl :=
	class_kw (tag "class" input)

@[partial]
def class_kw (r : ParseResult String) : ParseResult Decl :=
	match r {
		success rem _ => class_constraints_or_name rem,
		fail e => fail e
	}

@[partial]
def class_constraints_or_name (input : String) : ParseResult Decl :=
	class_try_constraints (tag "[" (skip_spaces input)) input

@[partial]
def class_try_constraints (r : ParseResult String) (orig : String) : ParseResult Decl :=
	match r {
		success rem _ => class_name_after_bracket rem,
		fail _ => class_name (identifier (skip_spaces orig))
	}

@[partial]
def class_name_after_bracket (input : String) : ParseResult Decl :=
	class_find_bracket_close (take_while is_not_bracket input) input

@[partial]
def class_find_bracket_close (r : ParseResult String) (orig : String) : ParseResult Decl :=
	match r {
		success rem _ => class_name_after_close (tag "]" rem) orig,
		fail _ => fail (ParseError.custom "expected ]")
	}

@[partial]
def class_name_after_close (r : ParseResult String) (orig : String) : ParseResult Decl :=
	match r {
		success rem _ => class_name (identifier (skip_spaces rem)),
		fail _ => class_name (identifier (skip_spaces orig))
	}

@[partial]
def class_name (r : ParseResult String) : ParseResult Decl :=
	match r {
		success rem name =>
			let empty_params : List Identifier := List.empty in
			class_params rem (Identifier.id name) empty_params,
		fail e => fail e
	}

@[partial]
def class_params (input : String) (name : Identifier) (params : List Identifier) : ParseResult Decl :=
	class_params_try (identifier (skip_spaces input)) input name params

@[partial]
def class_params_try (r : ParseResult String) (orig : String) (name : Identifier) (params : List Identifier) : ParseResult Decl :=
	match r {
		success rem next => class_params rem name (List.cons (Identifier.id next) params),
		fail _ => class_try_paren (tag "(" (skip_spaces orig)) orig name
	}

@[partial]
def class_try_paren (r : ParseResult String) (orig : String) (name : Identifier) : ParseResult Decl :=
	match r {
		success rem _ =>
			class_paren_close (take_while is_not_close_paren rem) rem orig name,
		fail _ => class_brace (tag "{" (skip_spaces orig)) name
	}

@[partial]
def class_paren_close (r : ParseResult String) (rem : String) (orig : String) (name : Identifier) : ParseResult Decl :=
	match r {
		success after _ =>
			class_paren_end (tag ")" (skip_spaces after)) after orig name,
		fail _ => class_brace (tag "{" (skip_spaces orig)) name
	}

@[partial]
def class_paren_end (r : ParseResult String) (orig : String) (orig2 : String) (name : Identifier) : ParseResult Decl :=
	match r {
		success rem _ =>
			class_try_more_parens_or_brace (tag "(" (skip_spaces rem)) rem name,
		fail _ => class_brace (tag "{" (skip_spaces orig)) name
	}

@[partial]
def class_try_more_parens_or_brace (r : ParseResult String) (orig : String) (name : Identifier) : ParseResult Decl :=
	match r {
		success rem _ =>
			class_paren_close (take_while is_not_close_paren rem) rem orig name,
		fail _ => class_brace (tag "{" (skip_spaces orig)) name
	}

@[partial]
def class_brace (r : ParseResult String) (name : Identifier) : ParseResult Decl :=
	match r {
		success rem _ =>
			let empty_methods : List ClassDef := List.empty in
			class_methods rem name empty_methods,
		fail e => fail e
	}

@[partial]
def class_methods (input : String) (name : Identifier) (methods : List ClassDef) : ParseResult Decl :=
	class_try_close_or_method (tag "def" (skip_spaces input)) input name methods

@[partial]
def class_try_close_or_method (r : ParseResult String) (orig : String) (name : Identifier) (methods : List ClassDef) : ParseResult Decl :=
	match r {
		success rem _ => class_methods_single rem name methods,
		fail _ => class_close (tag "}" (skip_spaces orig)) name methods
	}

@[partial]
def class_methods_single (input : String) (name : Identifier) (methods : List ClassDef) : ParseResult Decl :=
	class_method_name (identifier (skip_spaces input)) name methods

@[partial]
def class_method_name (r : ParseResult String) (name : Identifier) (methods : List ClassDef) : ParseResult Decl :=
	match r {
		success rem mname => class_method_colon_or_sig rem (Identifier.id mname) name methods,
		fail e => fail e
	}

@[partial]
def class_method_colon_or_sig (input : String) (mname : Identifier) (name : Identifier) (methods : List ClassDef) : ParseResult Decl :=
	class_method_params_try (tag "(" (skip_spaces input)) input mname name methods

@[partial]
def class_method_params_try (r : ParseResult String) (orig : String) (mname : Identifier) (name : Identifier) (methods : List ClassDef) : ParseResult Decl :=
	match r {
		success rem _ => class_method_param_loop rem mname name methods,
		fail _ => class_method_ret_type (tag ":" (skip_spaces orig)) mname name methods
	}

@[partial]
def class_method_param_loop (input : String) (mname : Identifier) (name : Identifier) (methods : List ClassDef) : ParseResult Decl :=
	class_method_one_param (identifier (skip_spaces input)) input mname name methods

@[partial]
def class_method_one_param (r : ParseResult String) (orig : String) (mname : Identifier) (name : Identifier) (methods : List ClassDef) : ParseResult Decl :=
	match r {
		success rem pname => class_method_param_colon (tag ":" (skip_spaces rem)) mname name methods orig,
		fail e => fail e
	}

@[partial]
def class_method_param_colon (r : ParseResult String) (mname : Identifier) (name : Identifier) (methods : List ClassDef) (orig : String) : ParseResult Decl :=
	match r {
		success rem _ =>
			let empty_ctx : List Identifier := List.empty in
			class_method_param_type (type_expression empty_ctx rem) mname name methods orig,
		fail e => fail e
	}

@[partial]
def class_method_param_type (r : ParseResult Term) (mname : Identifier) (name : Identifier) (methods : List ClassDef) (orig : String) : ParseResult Decl :=
	match r {
		success rem _ => class_method_close_or_next rem mname name methods orig,
		fail e => fail e
	}

@[partial]
def class_method_close_or_next (input : String) (mname : Identifier) (name : Identifier) (methods : List ClassDef) (orig : String) : ParseResult Decl :=
	class_method_try_close_param (tag ")" (skip_spaces input)) input mname name methods

@[partial]
def class_method_try_close_param (r : ParseResult String) (orig : String) (mname : Identifier) (name : Identifier) (methods : List ClassDef) : ParseResult Decl :=
	match r {
		success rem _ => class_method_ret_or_more rem mname name methods,
		fail _ => class_method_next_param (tag "(" (skip_spaces orig)) orig mname name methods
	}

@[partial]
def class_method_ret_or_more (input : String) (mname : Identifier) (name : Identifier) (methods : List ClassDef) : ParseResult Decl :=
	class_method_try_ret_type (tag ":" (skip_spaces input)) input mname name methods

@[partial]
def class_method_try_ret_type (r : ParseResult String) (orig : String) (mname : Identifier) (name : Identifier) (methods : List ClassDef) : ParseResult Decl :=
	match r {
		success rem _ =>
			let empty_ctx : List Identifier := List.empty in
			class_method_ret_type_val (type_expression empty_ctx rem) mname name methods,
		fail _ => class_method_next_param (tag "(" (skip_spaces orig)) orig mname name methods
	}

@[partial]
def class_method_ret_type_val (r : ParseResult Term) (mname : Identifier) (name : Identifier) (methods : List ClassDef) : ParseResult Decl :=
	match r {
		success rem typ => class_method_default_or_done rem mname typ name methods,
		fail e => fail e
	}

@[partial]
def class_method_next_param (r : ParseResult String) (orig : String) (mname : Identifier) (name : Identifier) (methods : List ClassDef) : ParseResult Decl :=
	match r {
		success rem _ => class_method_param_loop rem mname name methods,
		fail _ => fail (ParseError.custom "expected ) or another parameter")
	}

@[partial]
def class_method_ret_type (r : ParseResult String) (mname : Identifier) (name : Identifier) (methods : List ClassDef) : ParseResult Decl :=
	match r {
		success rem _ =>
			let empty_ctx : List Identifier := List.empty in
			class_method_sig_type (type_expression empty_ctx rem) mname name methods,
		fail _ => fail (ParseError.custom "expected : return type")
	}

@[partial]
def class_method_sig_type (r : ParseResult Term) (mname : Identifier) (name : Identifier) (methods : List ClassDef) : ParseResult Decl :=
	match r {
		success rem typ => class_method_default_or_done rem mname typ name methods,
		fail e => fail e
	}

@[partial]
def class_method_default_or_done (input : String) (mname : Identifier) (typ : Term) (name : Identifier) (methods : List ClassDef) : ParseResult Decl :=
	class_method_try_default (tag ":=" (skip_spaces input)) input mname typ name methods

@[partial]
def class_method_try_default (r : ParseResult String) (orig : String) (mname : Identifier) (typ : Term) (name : Identifier) (methods : List ClassDef) : ParseResult Decl :=
	match r {
		success rem _ =>
			let empty_ctx : List Identifier := List.empty in
			class_method_default_val (expression empty_ctx (skip_spaces rem)) orig mname typ name methods,
		fail _ =>
			let none_val : Option Term := Option.none in
			class_methods orig name (List.cons (ClassDef.mk mname typ none_val) methods)
	}

@[partial]
def class_method_default_val (r : ParseResult Term) (orig : String) (mname : Identifier) (typ : Term) (name : Identifier) (methods : List ClassDef) : ParseResult Decl :=
	match r {
		success rem defval =>
			let some_val : Option Term := Option.some defval in
			class_methods rem name (List.cons (ClassDef.mk mname typ some_val) methods),
		fail e => fail e
	}

@[partial]
def class_close (r : ParseResult String) (name : Identifier) (methods : List ClassDef) : ParseResult Decl :=
	match r {
		success rem _ =>
			let rev_methods : List ClassDef := list_reverse methods in
			let empty_params : List Param := List.empty in
			let empty_constraints : List TypeConstraint := List.empty in
			success rem (Decl.class_d (Class.mk name empty_params empty_constraints rev_methods)),
		fail e => fail e
	}

// instance [constraints] Class args { def method := body }
//
// Same shape as class_parser above: optional `[...]` constraints, the
// class name, zero-or-more argument terms (instance_args_or_brace loop),
// then a brace-delimited list of `def name (params) := body` method
// implementations (instance_methods loop; instance_method_* parses one
// method).

@[partial]
def instance_parser (input : String) : ParseResult Decl :=
	instance_kw (tag "instance" input)

@[partial]
def instance_kw (r : ParseResult String) : ParseResult Decl :=
	match r {
		success rem _ => instance_try_constraints (tag "[" (skip_spaces rem)) rem,
		fail e => fail e
	}

@[partial]
def instance_try_constraints (r : ParseResult String) (orig : String) : ParseResult Decl :=
	match r {
		success rem _ => instance_parse_bracket rem,
		fail _ => instance_name (module_path_parser (skip_spaces orig))
	}

@[partial]
def instance_parse_bracket (input : String) : ParseResult Decl :=
	instance_constraints_with_bracket (take_while is_not_bracket input) input

@[partial]
def instance_constraints_with_bracket (r : ParseResult String) (orig : String) : ParseResult Decl :=
	match r {
		success rem content =>
			instance_constraints_then_name (type_constraint_list content) rem,
		fail _ => fail (ParseError.custom "expected ]")
	}

@[partial]
def instance_constraints_then_name (cr : ParseResult (List TypeConstraint)) (input : String) : ParseResult Decl :=
	match cr {
		success _ constraints =>
			instance_constraints_close_bracket (tag "]" input) constraints,
		fail _ =>
			let empty_cs : List TypeConstraint := List.empty in
			instance_constraints_close_bracket (tag "]" input) empty_cs
	}

@[partial]
def instance_constraints_close_bracket (r : ParseResult String) (constraints : List TypeConstraint) : ParseResult Decl :=
	match r {
		success rem _ =>
			instance_set_constraints (instance_name (module_path_parser (skip_spaces rem))) constraints,
		fail _ => fail (ParseError.custom "expected ] after instance constraint")
	}

@[partial]
def instance_set_constraints (dr : ParseResult Decl) (constraints : List TypeConstraint) : ParseResult Decl :=
	match dr {
		success rem decl =>
			match decl {
				instance_d inst =>
					match inst {
						Instance.mk name cls _ args =>
							success rem (Decl.instance_d (Instance.mk name cls constraints args))
					},
				_ => success rem decl
			},
		fail e => fail e
	}

@[partial]
def instance_name (r : ParseResult ModulePath) : ParseResult Decl :=
	match r {
		success rem path =>
			let empty_args : List Term := List.empty in
			instance_args_or_brace rem path empty_args,
		fail e => fail e
	}

@[partial]
def instance_args_or_brace (input : String) (cls : ModulePath) (args : List Term) : ParseResult Decl :=
	let empty_ctx : List Identifier := List.empty in
	instance_try_arg (atom_term empty_ctx (skip_spaces input)) input cls args

@[partial]
def instance_try_arg (r : ParseResult Term) (orig : String) (cls : ModulePath) (args : List Term) : ParseResult Decl :=
	match r {
		success rem arg => instance_args_or_brace rem cls (List.cons arg args),
		fail _ => instance_brace (tag "{" (skip_spaces orig)) cls args
	}

@[partial]
def instance_brace (r : ParseResult String) (cls : ModulePath) (args : List Term) : ParseResult Decl :=
	match r {
		success rem _ =>
			let empty_methods : List Def := List.empty in
			instance_methods rem cls args empty_methods,
		fail e => fail e
	}

@[partial]
def instance_methods (input : String) (cls : ModulePath) (args : List Term) (methods : List Def) : ParseResult Decl :=
	instance_try_close_or_def (tag "def" (skip_spaces input)) input cls args methods

@[partial]
def instance_try_close_or_def (r : ParseResult String) (orig : String) (cls : ModulePath) (args : List Term) (methods : List Def) : ParseResult Decl :=
	match r {
		success rem _ => instance_method_single rem cls args methods,
		fail _ => instance_close (tag "}" (skip_spaces orig)) cls args methods
	}

@[partial]
def instance_method_single (input : String) (cls : ModulePath) (args : List Term) (methods : List Def) : ParseResult Decl :=
	instance_method_name (identifier (skip_spaces input)) cls args methods

@[partial]
def instance_method_name (r : ParseResult String) (cls : ModulePath) (args : List Term) (methods : List Def) : ParseResult Decl :=
	match r {
		success rem name => instance_method_params_or_body rem (Identifier.id name) cls args methods,
		fail e => fail e
	}

@[partial]
def instance_method_params_or_body (input : String) (name : Identifier) (cls : ModulePath) (args : List Term) (methods : List Def) : ParseResult Decl :=
	let empty_ctx : List Identifier := List.empty in
	instance_method_try_body (atom_term empty_ctx (skip_spaces input)) input name cls args methods

@[partial]
def instance_method_try_body (r : ParseResult Term) (orig : String) (name : Identifier) (cls : ModulePath) (args : List Term) (methods : List Def) : ParseResult Decl :=
	match r {
		success rem arg =>
			let start_args : List Term := List.cons arg List.empty in
			instance_method_body_loop rem start_args name cls args methods,
		fail _ => instance_method_finish (tag ":=" (skip_spaces orig)) name cls args methods
	}

@[partial]
def instance_method_body_loop (input : String) (body_args : List Term) (name : Identifier) (cls : ModulePath) (args : List Term) (methods : List Def) : ParseResult Decl :=
	let empty_ctx : List Identifier := List.empty in
	instance_method_body_next (atom_term empty_ctx (skip_spaces input)) input body_args name cls args methods

@[partial]
def instance_method_body_next (r : ParseResult Term) (orig : String) (body_args : List Term) (name : Identifier) (cls : ModulePath) (args : List Term) (methods : List Def) : ParseResult Decl :=
	match r {
		success rem arg => instance_method_body_loop rem (List.cons arg body_args) name cls args methods,
		fail _ => instance_method_finish (tag ":=" (skip_spaces orig)) name cls args methods
	}

@[partial]
def instance_method_finish (r : ParseResult String) (name : Identifier) (cls : ModulePath) (args : List Term) (methods : List Def) : ParseResult Decl :=
	match r {
		success rem _ =>
			let empty_ctx : List Identifier := List.empty in
			instance_method_body (expression empty_ctx (skip_spaces rem)) name cls args methods,
		fail _ => fail (ParseError.custom "expected := in instance method")
	}

@[partial]
def instance_method_body (r : ParseResult Term) (name : Identifier) (cls : ModulePath) (args : List Term) (methods : List Def) : ParseResult Decl :=
	match r {
		success rem body =>
			let empty_constraints : List TypeConstraint := List.empty in
			let empty_attrs : List String := List.empty in
			let d : Def := Def.mk (ModulePath.mp (List.cons name List.empty)) (Term.hole) body empty_constraints empty_attrs in
			instance_methods rem cls args (List.cons d methods),
		fail e => fail e
	}

@[partial]
def instance_close (r : ParseResult String) (cls : ModulePath) (args : List Term) (methods : List Def) : ParseResult Decl :=
	match r {
		success rem _ =>
			let rev_methods : List Def := list_reverse methods in
			let rev_args : List Term := list_reverse args in
			let empty_constraints : List TypeConstraint := List.empty in
			success rem (Decl.instance_d (Instance.mk (Identifier.id "_") cls empty_constraints rev_args)),
		fail e => fail e
	}

// Canonical decl dispatcher

def decl_parsers : List (String -> ParseResult Decl) :=
	[use_parser, open_parser, infix_parser, def_parser,
	 struct_parser, type_parser, class_parser, instance_parser]

@[partial]
def decl_parser (input : String) : ParseResult Decl :=
	decl_fail_to_unknown (alt_fold decl_parsers input)

@[partial]
def decl_fail_to_unknown (r : ParseResult Decl) : ParseResult Decl :=
	match r {
		success rem out => success rem out,
		fail _ => fail (ParseError.custom "unknown declaration")
	}

// ─── Multiple declaration parser (file-level) ──────────────────────────

@[partial]
def decls_parser (input : String) : ParseResult (List Decl) :=
	decls_skip (skip_docstrings (skip_spaces input)) List.empty

@[partial]
def decls_skip (input : String) (acc : List Decl) : ParseResult (List Decl) :=
	decls_try (decl_parser input) input acc

@[partial]
def decls_try (r : ParseResult Decl) (orig : String) (acc : List Decl) : ParseResult (List Decl) :=
	match r {
		success rem decl => decls_skip (skip_docstrings (skip_spaces rem)) (List.cons decl acc),
		fail _ => success orig (list_reverse acc)
	}

// Top-level declaration dispatcher

@[test]
def test_tag_hello : Bool :=
	match tag "hello" "hello world" {
		success rem out => String.beq rem " world",
		fail _ => false
	}

@[test]
def test_identifier_abc : Bool :=
	match identifier "abc def" {
		success rem out => String.beq out "abc" && String.beq rem " def",
		fail _ => false
	}

@[test]
def test_identifier_rejects_keyword : Bool :=
	match identifier "def x" {
		success _ _ => false,
		fail _ => true
	}

@[test]
def test_identifier_rejects_digit_start : Bool :=
	match identifier "123abc" {
		success _ _ => false,
		fail _ => true
	}

@[test]
def test_number_42 : Bool :=
	match number "42 abc" {
		success rem out => I64.beq out 42 && String.beq rem " abc",
		fail _ => false
	}

@[test]
def test_number_fail_empty : Bool :=
	match number "abc" {
		success _ _ => false,
		fail _ => true
	}

@[test]
def test_alt_tag : Bool :=
	match (alt (tag "foo") (tag "bar")) "foobar" {
		success rem out => String.beq out "foo" && String.beq rem "bar",
		fail _ => false
	}

@[test]
def test_many1_single : Bool :=
	match many1 (tag "a") "a" {
		success rem out => String.beq rem "",
		fail _ => false
	}

@[test]
def test_many1_multiple : Bool :=
	match many1 (tag "a") "aaab" {
		success rem out => String.beq rem "b",
		fail _ => false
	}

@[test]
def test_many1_fail : Bool :=
	match many1 (tag "a") "b" {
		success _ _ => false,
		fail _ => true
	}

@[test]
def test_do_empty : Bool :=
    let empty_ctx : List Identifier := List.empty in
    match do_parser empty_ctx "do { }" {
        success rem _ => String.beq rem "",
        fail _ => false
    }

@[test]
def test_do_return : Bool :=
    let empty_ctx : List Identifier := List.empty in
    match do_parser empty_ctx "do { return 42 }" {
        success rem _ => String.beq rem "",
        fail _ => false
    }

@[test]
def test_do_bind : Bool :=
    let empty_ctx : List Identifier := List.empty in
    match do_parser empty_ctx "do { let x <- m; return x }" {
        success rem _ => String.beq rem "",
        fail _ => false
    }

@[test]
def test_do_let : Bool :=
    let empty_ctx : List Identifier := List.empty in
    match do_parser empty_ctx "do { let x := 1; return x }" {
        success rem _ => String.beq rem "",
        fail _ => false
    }

@[test]
def test_do_expr : Bool :=
    let empty_ctx : List Identifier := List.empty in
    match do_parser empty_ctx "do { println 42; return 0 }" {
        success rem _ => String.beq rem "",
        fail _ => false
    }

@[test]
def test_do_chain : Bool :=
    let empty_ctx : List Identifier := List.empty in
    match do_parser empty_ctx "do { let a <- f x; let b <- g a; return b }" {
        success rem _ => String.beq rem "",
        fail _ => false
    }

@[test]
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

@[partial]
def id_str (s : String) : String := s

@[partial]
def str_len (s : String) : I64 := String.length s

@[partial]
def always_tag_y (a : String) (input : String) : ParseResult String := tag "y" input

@[test]
def test_map_parse_simple : Bool :=
	match map_parse id_str identifier "abc def" {
		success rem out => String.beq rem " def",
		fail _ => false
	}

@[test]
def test_map_parse_tag : Bool :=
	match map_parse id_str (tag "x") "xy" {
		success rem out => String.beq out "x",
		fail _ => false
	}

@[test]
def test_map_parse_fail : Bool :=
	match map_parse id_str (tag "x") "y" {
		success rem out => false,
		fail e => true
	}

@[test]
def test_map_parse_mapped : Bool :=
	match map_parse str_len identifier "abc def" {
		success rem out => String.beq rem " def",
		fail _ => false
	}

@[test]
def test_bind_parse : Bool :=
	match bind_parse (tag "x") always_tag_y "xyz" {
		success rem out => String.beq rem "z",
		fail _ => false
	}

@[test]
def test_bind_parse_fail_first : Bool :=
	match bind_parse (tag "x") always_tag_y "abc" {
		success rem out => false,
		fail e => true
	}

@[test]
def test_bind_parse_fail_second : Bool :=
	match bind_parse (tag "x") always_tag_y "xab" {
		success rem out => false,
		fail e => true
	}

@[test]
def test_alt_fold_first : Bool :=
	match alt_fold (List.cons (tag "a") (List.cons (tag "b") (List.cons (tag "c") List.empty))) "abc" {
		success rem out => String.beq rem "bc",
		fail _ => false
	}

@[test]
def test_alt_fold_second : Bool :=
	match alt_fold (List.cons (tag "x") (List.cons (tag "y") (List.cons (tag "z") List.empty))) "y" {
		success rem out => String.beq rem "",
		fail _ => false
	}

@[test]
def test_alt_fold_none : Bool :=
	match alt_fold (List.cons (tag "x") (List.cons (tag "y") List.empty)) "abc" {
		success rem out => false,
		fail e => true
	}

@[test]
def test_preceded_by : Bool :=
	match preceded_by (tag "(") (tag "x") "(x" {
		success rem out => String.beq rem "",
		fail _ => false
	}

@[test]
def test_preceded_by_fail : Bool :=
	match preceded_by (tag "(") (tag "x") "x" {
		success rem out => false,
		fail e => true
	}

@[test]
def test_terminated_by : Bool :=
	match terminated_by (tag "x") (tag ")") "x)" {
		success rem out => String.beq rem "",
		fail _ => false
	}

@[test]
def test_terminated_by_fail : Bool :=
	match terminated_by (tag "x") (tag ")") "x(" {
		success rem out => false,
		fail e => true
	}

@[test]
def test_delimited_by : Bool :=
	match delimited_by (tag "(") (tag "x") (tag ")") "(x)" {
		success rem out => String.beq rem "",
		fail _ => false
	}

@[test]
def test_delimited_by_fail_open : Bool :=
	match delimited_by (tag "(") (tag "x") (tag ")") "x)" {
		success rem out => false,
		fail e => true
	}

@[test]
def test_delimited_by_fail_close : Bool :=
	match delimited_by (tag "(") (tag "x") (tag ")") "(x(" {
		success rem out => false,
		fail e => true
	}

@[test]
def test_separated_by_single : Bool :=
	match separated_by (tag ",") (tag "a") "a" {
		success rem out => String.beq rem "",
		fail _ => false
	}

@[test]
def test_separated_by_multi : Bool :=
	match separated_by (tag ",") (tag "a") "a,a,a" {
		success rem out => String.beq rem "",
		fail _ => false
	}

@[test]
def test_separated_by_empty : Bool :=
	match separated_by (tag ",") (tag "a") "b" {
		success rem out => String.beq rem "b",
		fail e => false
	}

@[test]
def test_opt_some : Bool :=
	match opt (tag "x") "xy" {
		success rem out => match out {
			Option.some val => String.beq val "x",
			Option.none => false
		},
		fail _ => false
	}

@[test]
def test_opt_none : Bool :=
	match opt (tag "x") "yz" {
		success rem out => match out {
			Option.some val => false,
			Option.none => String.beq rem "yz"
		},
		fail _ => false
	}

@[test]
def test_ws0 : Bool :=
	match ws0 "  abc" {
		success rem out => String.beq rem "abc",
		fail _ => false
	}

@[test]
def test_ws0_empty : Bool :=
	match ws0 "abc" {
		success rem out => String.beq rem "abc",
		fail _ => false
	}

@[test]
def test_ws1 : Bool :=
	match ws1 "  abc" {
		success rem out => String.beq rem "abc",
		fail _ => false
	}

@[test]
def test_ws1_fail : Bool :=
	match ws1 "abc" {
		success rem out => false,
		fail e => true
	}

// --- Position tracking tests (Phase 1.2) ---

@[test]
def test_new_span : Bool :=
	let span : LocatedSpan := new_span "hello" in
	let frag : String := span_fragment span in
	I64.beq (String.length frag) 5

@[test]
def test_new_span_location : Bool :=
	let span : LocatedSpan := new_span "x" in
	let loc : Location := span_location span in
	match loc {
		mk off line col => I64.beq off 0 && I64.beq line 1 && I64.beq col 1
	}

@[test]
def test_consume_no_newline : Bool :=
	let span : LocatedSpan := new_span "hello world" in
	let next : LocatedSpan := consume_span span 5 in
	let loc : Location := span_location next in
	match loc {
		mk off line col => I64.beq off 5 && I64.beq line 1 && I64.beq col 6
	}

@[test]
def test_consume_single_newline : Bool :=
	let span : LocatedSpan := new_span "a\nb" in
	let next : LocatedSpan := consume_span span 2 in
	let loc : Location := span_location next in
	match loc {
		mk off line col => I64.beq off 2 && I64.beq line 2 && I64.beq col 1
	}

@[test]
def test_consume_multi_newline : Bool :=
	let span : LocatedSpan := new_span "a\n\nb" in
	let next : LocatedSpan := consume_span span 3 in
	let loc : Location := span_location next in
	match loc {
		mk off line col => I64.beq off 3 && I64.beq line 3 && I64.beq col 1
	}

@[test]
def test_span_fragment_after_consume : Bool :=
	let span : LocatedSpan := new_span "hello world" in
	let next : LocatedSpan := consume_span span 6 in
	let rest : String := span_fragment next in
	String.beq rest "world"

def sentinel : I64 := -1

@[partial]
def ident_str (id: Identifier) : String :=
    match id {
        id s => s
    }

@[partial]
def find_index (id: Identifier) (ctx: List Identifier) (depth: I64) : Option I64 :=
    match ctx {
        List.cons x rest =>
            if String.beq (ident_str id) (ident_str x)
            then Option.some depth
            else find_index id rest (depth + 1),
        List.empty => Option.none
    }

@[partial]
def debug_name_of_id (id: Identifier) : DebugName :=
    DebugName.named id

@[partial]
def var_term (ctx: List Identifier) (s: String) : Term :=
    let sid : Identifier := Identifier.id s in
    match find_index sid ctx 0 {
        Option.some idx => Term.var idx (DebugName.named sid),
        Option.none => Term.var sentinel (DebugName.named sid)
    }

@[partial]
def variable (ctx: List Identifier) (input: String) : ParseResult Term :=
    variable_try_path (path_variable input) ctx input

@[partial]
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

@[partial]
def variable_got (r: ParseResult String) (ctx: List Identifier) : ParseResult Term :=
    match r {
        success rem out => success rem (var_term ctx out),
        fail e => fail e
    }

// ─── Canonical literal parser (Phase 10) ───────────────────────────────

def num_to_term (n: I64) : Term :=
    Term.lit (Literal.num n NumSuffix.i64)

@[partial]
def number_term (input: String) : ParseResult Term :=
    map_parse num_to_term number input

@[partial]
def literal_parser (input: String) : ParseResult Term :=
    alt_fold [string_parse, number_term] input

// Skip /// docstring lines (consumed as whitespace).
@[partial]
def skip_docstrings (input : String) : String :=
	skip_docstrings_try (tag "///" input) input

@[partial]
def skip_docstrings_try (r : ParseResult String) (orig : String) : String :=
	match r {
		success rem _ => skip_docstrings_eol (take_while is_not_newline rem) rem,
		fail _ => orig
	}

@[partial]
def skip_docstrings_eol (r : ParseResult String) (orig : String) : String :=
	let after_eol : String := skip_spaces_match r orig in
	skip_docstrings_try_newline (tag "\n" after_eol) after_eol

@[partial]
def skip_docstrings_try_newline (r : ParseResult String) (orig : String) : String :=
	match r {
		success rem _ => skip_docstrings (skip_spaces rem),
		fail _ => orig
	}

// ─── Term atom ──────────────────────────────────────────────────────────

@[partial]
def atom_term (ctx: List Identifier) (input: String) : ParseResult Term :=
    match alt_fold (atom_parsers ctx) input {
        success rem out => success rem out,
        fail _ =>
            match lambda_parser ctx input {
                success rem out => success rem out,
                fail _ => paren_expr ctx input
            }
    }

@[partial]
def atom_parsers (ctx: List Identifier) : List (String -> ParseResult Term) :=
    [variable ctx, literal_parser, match_parser ctx, if_parser ctx]

// ─── Canonical match case parser (Phase 9) ─────────────────────────────

@[partial]
def match_case_parser (ctx: List Identifier) (input: String) : ParseResult MatchCase :=
    match_case_name (identifier (skip_spaces input)) ctx

@[partial]
def match_case_name (r: ParseResult String) (ctx: List Identifier) : ParseResult MatchCase :=
    match r {
        success rem name =>
            match_case_args (many0 identifier (skip_spaces rem)) (Identifier.id name) ctx,
        fail e => fail e
    }

@[partial]
def match_case_args (r: ParseResult (List String)) (name: Identifier) (ctx: List Identifier) : ParseResult MatchCase :=
    match r {
        success rem _ => match_case_arrow (tag "=>" (skip_spaces rem)) name ctx,
        fail e => fail e
    }

@[partial]
def match_case_arrow (r: ParseResult String) (name: Identifier) (ctx: List Identifier) : ParseResult MatchCase :=
    match r {
        success rem _ => match_case_body (expression ctx (skip_spaces rem)) name,
        fail e => fail e
    }

@[partial]
def match_case_body (r: ParseResult Term) (name: Identifier) : ParseResult MatchCase :=
    match r {
        success rem body =>
            let empty_args : List Identifier := List.empty in
            success (match_case_tail rem) (MatchCase.mc name empty_args body),
        fail e => fail e
    }

@[partial]
def match_case_tail (input: String) : String :=
    match take_while is_space input {
        success after_sp _ =>
            match tag "," after_sp {
                success rem _ => skip_spaces rem,
                fail _ => after_sp
            },
        fail _ => input
    }

// ─── Canonical match expression parser (Phase 9) ───────────────────────

@[partial]
def match_parser (ctx: List Identifier) (input: String) : ParseResult Term :=
    match_kw (tag "match" input) ctx

@[partial]
def match_kw (r: ParseResult String) (ctx: List Identifier) : ParseResult Term :=
    match r {
        success rem _ => match_scrutinee (expression ctx (skip_spaces rem)) ctx,
        fail e => fail e
    }

@[partial]
def match_scrutinee (r: ParseResult Term) (ctx: List Identifier) : ParseResult Term :=
    match r {
        success rem scrutinee => match_brace_open (tag "{" (skip_spaces rem)) scrutinee ctx,
        fail e => fail e
    }

@[partial]
def match_brace_open (r: ParseResult String) (scrutinee: Term) (ctx: List Identifier) : ParseResult Term :=
    match r {
        success rem _ => match_cases_parse (many1 (match_case_parser ctx) rem) scrutinee,
        fail e => fail e
    }

@[partial]
def match_cases_parse (r: ParseResult (List MatchCase)) (scrutinee: Term) : ParseResult Term :=
    match r {
        success rem cases => match_close (tag "}" (skip_spaces rem)) scrutinee cases,
        fail e => fail e
    }

@[partial]
def match_close (r: ParseResult String) (scrutinee: Term) (cases: List MatchCase) : ParseResult Term :=
    match r {
        success rem _ => success rem (Term.lit (Literal.match_ scrutinee cases)),
        fail e => fail e
    }

// ─── Canonical if expression parser (Phase 9) ─────────────────────────

@[partial]
def if_parser (ctx: List Identifier) (input: String) : ParseResult Term :=
    if_kw (tag "if" input) ctx

@[partial]
def if_kw (r: ParseResult String) (ctx: List Identifier) : ParseResult Term :=
    match r {
        success rem _ => if_cond (expression ctx (skip_spaces rem)) ctx,
        fail e => fail e
    }

@[partial]
def if_cond (r: ParseResult Term) (ctx: List Identifier) : ParseResult Term :=
    match r {
        success rem cond => if_then_kw (tag "then" (skip_spaces rem)) cond ctx,
        fail e => fail e
    }

@[partial]
def if_then_kw (r: ParseResult String) (cond: Term) (ctx: List Identifier) : ParseResult Term :=
    match r {
        success rem _ => if_then_branch (expression ctx (skip_spaces rem)) cond ctx,
        fail e => fail e
    }

@[partial]
def if_then_branch (r: ParseResult Term) (cond: Term) (ctx: List Identifier) : ParseResult Term :=
    match r {
        success rem then_b => if_else_kw (tag "else" (skip_spaces rem)) cond then_b ctx,
        fail e => fail e
    }

@[partial]
def if_else_kw (r: ParseResult String) (cond: Term) (then_b: Term) (ctx: List Identifier) : ParseResult Term :=
    match r {
        success rem _ => if_else_branch (expression ctx (skip_spaces rem)) cond then_b,
        fail e => fail e
    }

@[partial]
def if_else_branch (r: ParseResult Term) (cond: Term) (then_b: Term) : ParseResult Term :=
    match r {
        success rem else_b => success rem (Term.lit (Literal.if_ cond then_b else_b)),
        fail e => fail e
    }

@[partial]
def paren_expr (ctx: List Identifier) (input: String) : ParseResult Term :=
    match tag "(" input {
        success rem _ => paren_inner (type_expression ctx rem),
        fail e => fail e
    }

@[partial]
def paren_inner (r: ParseResult Term) : ParseResult Term :=
    match r {
        success rem out => paren_close (tag ")" rem) out,
        fail e => fail e
    }

@[partial]
def paren_close (r: ParseResult String) (out: Term) : ParseResult Term :=
    match r {
        success rem _ => success rem out,
        fail e => fail e
    }

// ─── Term lambda ────────────────────────────────────────────────────────

@[partial]
def lambda_parser (ctx: List Identifier) (input: String) : ParseResult Term :=
    lambda_kw (alt (alt (tag "fn") (tag "ꟛ")) (tag "\\") input) ctx

@[partial]
def lambda_kw (r: ParseResult String) (ctx: List Identifier) : ParseResult Term :=
    match r {
        success rem _ => lambda_name_outer (skip_spaces rem) ctx,
        fail e => fail e
    }

@[partial]
def lambda_name_outer (input: String) (ctx: List Identifier) : ParseResult Term :=
    lambda_name_outer_got (identifier input) input ctx

@[partial]
def lambda_name_outer_got (r: ParseResult String) (orig: String) (ctx: List Identifier) : ParseResult Term :=
    match r {
        success rem name => lambda_arrow (tag "=>" (skip_spaces rem)) rem orig (Identifier.id name) ctx,
        fail e => fail e
    }

@[partial]
def lambda_arrow (r: ParseResult String) (rem: String) (orig: String) (name: Identifier) (ctx: List Identifier) : ParseResult Term :=
    match r {
        success rem2 _ => lambda_body (expression (List.cons name ctx) (skip_spaces rem2)) name,
        fail e => fail e
    }

@[partial]
def lambda_body (r: ParseResult Term) (name: Identifier) : ParseResult Term :=
    match r {
        success rem body => success rem (Term.lam (DebugName.named name) (Term.type_ 1) body),
        fail e => fail e
    }

// ─── Term expression (application + operators) ─────────────────────────
//
// Simple recursive-descent, not a full Pratt/precedence-climbing parser:
// 1. Parse one atom as the left-hand side (expr_first).
// 2. Repeatedly try to parse another atom and apply it (juxtaposition,
//    e.g. `f x y`) — expr_rest/expr_rest_next loop until that fails.
// 3. Once no more bare atoms apply, look for an infix operator
//    (expr_op/expr_op_try). An operator with precedence 0 in op_table
//    (core.mo) — i.e. not a recognized operator — stops parsing here
//    (expr_op_prec_val) rather than erroring, so the caller can try to
//    consume it as something else.
// 4. Otherwise recurse into `expression` again for the right-hand side
//    (expr_op_rhs_ws/expr_op_rhs_expr) — this makes every recognized
//    operator right-associative by construction. op_table's own
//    right_assoc flag (op_lookup_rassoc, core.mo) is never consulted by
//    this parser at all — only op_precedence's "is this a known operator"
//    check is used.

@[partial]
def expression (ctx: List Identifier) (input: String) : ParseResult Term :=
    expr_first (atom_term ctx (skip_spaces input)) ctx

@[partial]
def expr_first (r: ParseResult Term) (ctx: List Identifier) : ParseResult Term :=
    match r {
        success rem lhs => expr_rest rem lhs ctx,
        fail e => fail e
    }

@[partial]
def expr_rest (input: String) (lhs: Term) (ctx: List Identifier) : ParseResult Term :=
    expr_rest_ws (take_while is_space input) lhs ctx

@[partial]
def expr_rest_ws (r: ParseResult String) (lhs: Term) (ctx: List Identifier) : ParseResult Term :=
    match r {
        success rem _ => expr_rest_next (atom_term ctx rem) rem lhs ctx,
        fail e => fail e
    }

@[partial]
def expr_rest_next (r: ParseResult Term) (input: String) (lhs: Term) (ctx: List Identifier) : ParseResult Term :=
    match r {
        success rem rhs => expr_rest rem (Term.app lhs rhs) ctx,
        fail _ => expr_op input lhs ctx
    }

@[partial]
def expr_op (input: String) (lhs: Term) (ctx: List Identifier) : ParseResult Term :=
    expr_op_try (operator_parse input) input lhs ctx

@[partial]
def expr_op_try (r: ParseResult String) (input: String) (lhs: Term) (ctx: List Identifier) : ParseResult Term :=
    match r {
        success rem op => expr_op_prec input lhs op rem ctx,
        fail _ => success input lhs
    }

@[partial]
def expr_op_prec (input: String) (lhs: Term) (op: String) (rem: String) (ctx: List Identifier) : ParseResult Term :=
    expr_op_prec_val (op_precedence op) input lhs op rem ctx

@[partial]
def expr_op_prec_val (prec: I64) (input: String) (lhs: Term) (op: String) (rem: String) (ctx: List Identifier) : ParseResult Term :=
    if I64.beq prec 0
    then success input lhs
    else expr_op_rhs_ws (take_while is_space rem) lhs op ctx

@[partial]
def expr_op_rhs_ws (r: ParseResult String) (lhs: Term) (op: String) (ctx: List Identifier) : ParseResult Term :=
    match r {
        success rem _ => expr_op_rhs_expr (expression ctx rem) lhs op ctx,
        fail e => fail e
    }

@[partial]
def expr_op_rhs_expr (r: ParseResult Term) (lhs: Term) (op: String) (ctx: List Identifier) : ParseResult Term :=
    match r {
        success rem rhs =>
            // Operator desugars to: op lhs rhs → app (app (var SENTINEL op) lhs) rhs
            let op_var : Term := Term.var sentinel DebugName.unnamed in
            success rem (Term.app (Term.app op_var lhs) rhs),
        fail e => fail e
    }

// ─── Term type expression (like expression but with -> for pi) ─────────

@[partial]
def type_expression (ctx: List Identifier) (input: String) : ParseResult Term :=
    type_expr_ws (take_while is_space input) input ctx

@[partial]
def type_expr_ws (r: ParseResult String) (input: String) (ctx: List Identifier) : ParseResult Term :=
    match r {
        success rem _ => type_try_dep (tag "(" (skip_spaces rem)) input ctx,
        fail e => fail e
    }

@[partial]
def type_try_dep (r: ParseResult String) (input: String) (ctx: List Identifier) : ParseResult Term :=
    match r {
        success rem _ => type_dep_id (identifier (skip_spaces rem)) input ctx,
        fail _ => type_plain input ctx
    }

@[partial]
def type_dep_id (r: ParseResult String) (input: String) (ctx: List Identifier) : ParseResult Term :=
    match r {
        success rem name => type_dep_colon (tag ":" (skip_spaces rem)) input name ctx,
        fail _ => type_plain input ctx
    }

@[partial]
def type_dep_colon (r: ParseResult String) (input: String) (name: String) (ctx: List Identifier) : ParseResult Term :=
    match r {
        success rem _ => type_dep_typ (type_expression ctx (skip_spaces rem)) input name ctx,
        fail _ => type_plain input ctx
    }

@[partial]
def type_dep_typ (r: ParseResult Term) (input: String) (name: String) (ctx: List Identifier) : ParseResult Term :=
    match r {
        success rem typ => type_dep_close (tag ")" (skip_spaces rem)) input name typ ctx,
        fail _ => type_plain input ctx
    }

@[partial]
def type_dep_close (r: ParseResult String) (input: String) (name: String) (typ: Term) (ctx: List Identifier) : ParseResult Term :=
    match r {
        success rem _ => type_dep_arrow rem name typ ctx,
        fail _ => type_plain input ctx
    }

@[partial]
def type_dep_arrow (rem: String) (name: String) (typ: Term) (ctx: List Identifier) : ParseResult Term :=
    type_dep_arrow_ws (take_while is_space rem) rem name typ ctx

@[partial]
def type_dep_arrow_ws (r: ParseResult String) (rem: String) (name: String) (typ: Term) (ctx: List Identifier) : ParseResult Term :=
    match r {
        success rem2 _ => type_dep_arrow_tag (tag "->" rem2) rem name typ ctx,
        fail e => fail e
    }

@[partial]
def type_dep_arrow_tag (r: ParseResult String) (rem: String) (name: String) (typ: Term) (ctx: List Identifier) : ParseResult Term :=
    match r {
        success rem2 _ => type_dep_body (type_expression (List.cons (Identifier.id name) ctx) (skip_spaces rem2)) typ,
        fail _ => success rem typ
    }

@[partial]
def type_dep_body (r: ParseResult Term) (typ: Term) : ParseResult Term :=
    match r {
        success rem body => success rem (Term.pi typ body),
        fail e => fail e
    }

// Plain type expression (no dependent binding on LHS).

// Parses expression, then checks for non-dependent -> arrow.

@[partial]
def type_plain (input: String) (ctx: List Identifier) : ParseResult Term :=
    type_plain_expr (expression ctx input) ctx

@[partial]
def type_plain_expr (r: ParseResult Term) (ctx: List Identifier) : ParseResult Term :=
    match r {
        success rem lhs => type_check_arrow rem lhs ctx,
        fail e => fail e
    }

@[partial]
def type_check_arrow (input: String) (lhs: Term) (ctx: List Identifier) : ParseResult Term :=
    type_arrow_ws (take_while is_space input) input lhs ctx

@[partial]
def type_arrow_ws (r: ParseResult String) (input: String) (lhs: Term) (ctx: List Identifier) : ParseResult Term :=
    match r {
        success rem _ => type_arrow_tag (tag "->" rem) input lhs ctx,
        fail e => fail e
    }

@[partial]
def type_arrow_tag (r: ParseResult String) (input: String) (lhs: Term) (ctx: List Identifier) : ParseResult Term :=
    match r {
        success rem _ => type_arrow_rhs lhs (type_expression ctx (skip_spaces rem)),
        fail _ => success input lhs
    }

@[partial]
def type_arrow_rhs (lhs: Term) (r: ParseResult Term) : ParseResult Term :=
    match r {
        success rem rhs => success rem (Term.pi lhs rhs),
        fail e => fail e
    }

// ─── Phase 1.5: docstring and implicit params tests ───────────────────────────────

@[test]
def test_skip_docstrings_none : Bool :=
	let rem : String := skip_docstrings "use prelude" in
	String.beq rem "use prelude"

@[test]
def test_skip_docstrings_one : Bool :=
	let rem : String := skip_docstrings "/// doc\nuse prelude" in
	String.beq rem "use prelude"

@[test]
def test_skip_docstrings_multi : Bool :=
	let rem : String := skip_docstrings "/// line1\n/// line2\n\ndef x := 1" in
	String.beq rem "def x := 1"

@[test]
def test_decls_with_docstring : Bool :=
	match decls_parser "/// A test declaration\ndef x : I64 := 42" {
		success rem decls =>
			let rem_stripped : String := skip_spaces rem in
			String.beq rem_stripped "" && I64.beq (debug_decl_count decls) 1,
		fail _ => false
	}

@[test]
def test_type_implicit_params : Bool :=
	match type_parser "type Any { any {A : Type} (value : A) }" {
		success rem decl => String.beq rem "",
		fail _ => false
	}

@[test]
def test_type_implicit_no_parens : Bool :=
	match type_parser "type All { mk {A : Type} (val : A) }" {
		success rem decl => String.beq rem "",
		fail _ => false
	}

// --- TypeConstraint parsing tests ---

@[test]
def test_type_constraint_one_simple : Bool :=
	match type_constraint_one "Functor F" {
		success rem _ => String.beq rem "",
		fail _ => false
	}

@[test]
def test_type_constraint_one_two_vars : Bool :=
	match type_constraint_one "HAdd A A A" {
		success rem _ => String.beq rem "",
		fail _ => false
	}

@[test]
def test_type_constraint_one_no_vars : Bool :=
	match type_constraint_one "Show" {
		success rem _ => String.beq rem "",
		fail _ => false
	}

@[test]
def test_type_constraint_list_single : Bool :=
	match type_constraint_list "Functor F" {
		success rem _ => String.beq rem "",
		fail _ => false
	}

@[test]
def test_type_constraint_list_multi : Bool :=
	match type_constraint_list "Functor F, Applicative M" {
		success rem _ => String.beq rem "",
		fail _ => false
	}

@[test]
def test_type_constraint_list_empty : Bool :=
	match type_constraint_list "" {
		success rem _ => String.beq rem "",
		fail _ => false
	}

@[test]
def test_class_with_constraints : Bool :=
	match class_parser "class [Functor F] Applicative F { def pure (a : A) : F A }" {
		success rem _ => String.beq rem "",
		fail _ => false
	}

@[test]
def test_instance_with_constraints : Bool :=
  match instance_parser "instance [Show A] Show A { def m := a }" {
    success rem _ => String.beq rem "",
    fail _ => false
  }

@[test]
def test_class_with_paren_params : Bool :=
  match class_parser "class Functor (F : Type -> Type) { def map (f : A -> B) : F A -> F B }" {
    success rem _ => String.beq rem "",
    fail _ => false
  }

@[test]
def test_class_with_default_param : Bool :=
  match class_parser "class FromListLiteral (L : Type -> Type := List) { def cons (a : A) : L A -> L A }" {
    success rem _ => String.beq rem "",
    fail _ => false
  }

// ─── Term parser tests (Phase 1) ───────────────────────────────────────

@[test]
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

@[test]
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

@[test]
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

@[test]
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

@[test]
def test_t_lambda_nested : Bool :=
	// fn x => fn y => y  →  lam/named/x (lam/named/y (var 0))
	let empty_ctx : List Identifier := List.empty in
	match expression empty_ctx "fn x => fn y => y" {
		success rem out => String.beq rem "",
		fail _ => false
	}

@[test]
def test_t_app_simple : Bool :=
	// f x  →  app (var SENTINEL f) (var SENTINEL x)
	let empty_ctx : List Identifier := List.empty in
	match expression empty_ctx "f x" {
		success rem out => String.beq rem "",
		fail _ => false
	}

@[test]
def test_t_app_chain : Bool :=
	// f x y  →  app (app (var SENTINEL f) (var SENTINEL x)) (var SENTINEL y)
	let empty_ctx : List Identifier := List.empty in
	match expression empty_ctx "f x y" {
		success rem out => String.beq rem "",
		fail _ => false
	}

@[test]
def test_t_operator : Bool :=
	// a ++ b  →  app (app (var SENTINEL _) (var SENTINEL a)) (var SENTINEL b)
	let empty_ctx : List Identifier := List.empty in
	match expression empty_ctx "a ++ b" {
		success rem out => String.beq rem "",
		fail _ => false
	}

@[test]
def test_t_parens : Bool :=
	// (x)  →  var (SENTINEL, x)
	let empty_ctx : List Identifier := List.empty in
	match expression empty_ctx "(x)" {
		success rem out => String.beq rem "",
		fail _ => false
	}

@[test]
def test_t_literal_num : Bool :=
	// 42  →  lit (num 42 i64)
	let empty_ctx : List Identifier := List.empty in
	match expression empty_ctx "42" {
		success rem out => String.beq rem "",
		fail _ => false
	}

@[test]
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

@[test]
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

@[test]
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

@[test]
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

@[test]
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

@[test]
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

@[partial]
def use_filter_is_bare (filter : UseFilter) : Bool :=
    match filter {
        UseFilter.use_bare => true,
        _ => false
    }

@[partial]
def open_filter_is_all (filter : OpenFilter) : Bool :=
    match filter {
        OpenFilter.open_all => true,
        _ => false
    }

@[test]
def test_use_parser : Bool :=
    match use_parser "use prelude" {
        success rem out =>
            match out {
                use_d path filter => (String.beq rem "") && use_filter_is_bare filter,
                _ => false
            },
        fail _ => false
    }

@[test]
def test_open_parser : Bool :=
    match open_parser "open IO" {
        success rem out =>
            match out {
                open_d path filter => (String.beq rem "") && open_filter_is_all filter,
                _ => false
            },
        fail _ => false
    }

@[partial]
def use_item_is_glob (item : UseItem) : Bool :=
    match item {
        UseItem.use_glob => true,
        _ => false
    }

@[test]
def test_use_glob : Bool :=
    match use_parser "use io {*}" {
        success rem out =>
            match out {
                use_d path filter =>
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

@[test]
def test_use_empty_braces : Bool :=
    match use_parser "use io {}" {
        success rem out =>
            match out {
                use_d path filter =>
                    match filter {
                        UseFilter.use_items items => List.is_empty items,
                        _ => false
                    },
                _ => false
            },
        fail _ => false
    }

@[test]
def test_use_nested_simple : Bool :=
    match use_parser "use io {file {read}}" {
        success rem out =>
            match out {
                use_d path filter =>
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

@[test]
def test_use_nested_rename : Bool :=
    match use_parser "use io {file as f {read}}" {
        success rem out =>
            match out {
                use_d path filter =>
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

@[test]
def test_use_nested_deep : Bool :=
    match use_parser "use io {a {b {c}}}" {
        success rem out => String.beq rem "",
        fail _ => false
    }

@[test]
def test_use_multiple_rename : Bool :=
    match use_parser "use io {read as r, write as w}" {
        success rem out =>
            match out {
                use_d path filter =>
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

@[test]
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

@[test]
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

@[test]
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

@[test]
def test_infix_parser : Bool :=
    match infix_parser "infix (++) := List.append" {
        success rem out =>
            match out {
                infix_d op path => String.beq rem "",
                _ => false
            },
        fail _ => false
    }

@[test]
def test_infix_parser_with_precedence : Bool :=
    match infix_parser "infix:5 (++) := List.append" {
        success rem out =>
            match out {
                infix_d op path => String.beq rem "",
                _ => false
            },
        fail _ => false
    }

@[test]
def test_struct_parser : Bool :=
    match struct_parser "struct Point { x : I64, y : I64 }" {
        success rem out =>
            match out {
                struct_d s => String.beq rem "",
                _ => false
            },
        fail _ => false
    }

@[test]
def test_def_parser : Bool :=
    match def_parser "@[test] def f (x : I64) : I64 := x" {
        success rem out =>
            match out {
                def_d d => String.beq rem "",
                _ => false
            },
        fail _ => false
    }

// `#[...]` is the current attribute delimiter (`@[...]` above is the
// deprecated predecessor) — both must parse identically.
#[test]
def test_def_parser_hash_attr : Bool :=
    match def_parser "#[test] def f (x : I64) : I64 := x" {
        success rem out =>
            match out {
                def_d d => String.beq rem "",
                _ => false
            },
        fail _ => false
    }

@[test]
def test_def_do_block : Bool :=
    match def_parser "def main : Unit { return 0 }" {
        success rem out =>
            match out {
                def_d d => String.beq rem "",
                _ => false
            },
        fail _ => false
    }

@[test]
def test_class_parser : Bool :=
    match class_parser "class Show A { def show (a : A) : String }" {
        success rem out =>
            match out {
                class_d c => String.beq rem "",
                _ => false
            },
        fail _ => false
    }

@[test]
def test_instance_parser : Bool :=
    match instance_parser "instance Functor Maybe { def map f m := match m { some a => a, none => none } }" {
        success rem out =>
            match out {
                instance_d i => String.beq rem "",
                _ => false
            },
        fail _ => false
    }

@[test]
def test_decl_parser_def : Bool :=
    match decl_parser "def add (a: I64) (b: I64) : I64 := a + b" {
        success rem out =>
            match out {
                def_d d => String.beq rem "",
                _ => false
            },
        fail _ => false
    }

@[test]
def test_decl_parser_fail : Bool :=
    match decl_parser "foobar" {
        success rem out => false,
        fail _ => true
    }

// ─── AST debug helpers ───────────────────────────────────────────────────

@[partial]
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

@[partial]
def debug_decl_count (decls : List Decl) : I64 :=
    match decls {
        List.empty => 0,
        List.cons d rest => 1 + debug_decl_count rest
    }

// ─── Multi-declaration parser tests ──────────────────────────────────────────────────────

@[test]
def test_decls_empty : Bool :=
    match decls_parser "" {
        success rem decls =>
            String.beq rem "" && match decls {
                List.empty => true,
                List.cons _ _ => false
            },
        fail _ => false
    }

@[test]
def test_decls_whitespace_only : Bool :=
    match decls_parser "  " {
        success rem decls =>
            String.beq rem "" && match decls {
                List.empty => true,
                List.cons _ _ => false
            },
        fail _ => false
    }

@[test]
def test_decls_one_use : Bool :=
    match decls_parser "use prelude" {
        success rem decls => String.beq rem "",
        fail _ => false
    }

@[test]
def test_decls_two_parsed : Bool :=
    match decls_parser "use prelude open IO" {
        success rem decls => String.beq rem "",
        fail _ => false
    }

@[test]
def test_decls_def : Bool :=
    match decls_parser "def x : I64 := 42" {
        success rem decls => String.beq rem "",
        fail _ => false
    }

@[test]
def test_decls_decl_plus_noise : Bool :=
    match decls_parser "use prelude  garbage" {
        success rem decls => true,
        fail _ => false
    }

@[test]
def test_decls_count_two : Bool :=
    match decls_parser "use prelude open IO" {
        success rem decls =>
            String.beq rem "" && I64.beq (debug_decl_count decls) 2,
        fail _ => false
    }

@[test]
def test_decls_count_one : Bool :=
    match decls_parser "def x : I64 := 1" {
        success rem decls =>
            String.beq rem "" && I64.beq (debug_decl_count decls) 1,
        fail _ => false
    }

@[test]
def test_decls_kind_use : Bool :=
    match decls_parser "use prelude" {
        success rem decls =>
            match decls {
                List.cons d rest =>
                    match rest { List.empty => String.beq rem "", List.cons _ _ => false },
                List.empty => false
            },
        fail _ => false
    }

@[test]
def test_decls_type_decl : Bool :=
    match decls_parser "type Maybe A { some (a : A), none }" {
        success rem decls => String.beq rem "",
        fail _ => false
    }

@[test]
def test_decls_class : Bool :=
    match decls_parser "class Show A { def show (a : A) : String }" {
        success rem decls => String.beq rem "",
        fail _ => false
    }

@[test]
def test_decls_struct : Bool :=
    match decls_parser "struct Point { x : I64, y : I64 }" {
        success rem decls => String.beq rem "",
        fail _ => false
    }

@[test]
def test_decls_mixed : Bool :=
    match decls_parser "use prelude  open IO  def main : I64 := 42" {
        success rem decls =>
            String.beq rem "" && I64.beq (debug_decl_count decls) 3,
        fail _ => false
    }

// ─── Phase 1.5 integration tests ───────────────────────────────────────────

@[test]
def test_decls_fromlist_one_line : Bool :=
    match class_parser "class FromListLiteral (L : Type -> Type := List) { def cons (a : A) : L A -> L A }" {
        success rem _ => true,
        fail _ => false
    }

@[test]
def test_decls_prelude_features : Bool :=
    match decls_parser "\ntype Any {\n  any {A : Type} (value: A)\n}\n\nclass Functor (F: Type -> Type) {\n  def map (f: A -> B) : (F A) -> F B\n}\n\nclass FromListLiteral (L : Type -> Type := List) {\n  def cons (a : A) : L A -> L A\n  def empty : L A\n}\n\n/// HAdd\nclass [HAdd A A] Add A {\n  def add (a: A) (b: A) : A\n}\n\ninstance [Show A] Show (List A) {\n  def show xs := \"list\"\n}\n" {
        success rem decls =>
            I64.beq (debug_decl_count decls) 5,
        fail _ => false
    }

@[test]
def test_decls_fromlist_one_line_nl : Bool :=
    match class_parser "class FromListLiteral (L : Type -> Type := List) {\n  def cons (a : A) : L A -> L A\n}\n" {
        success rem _ => true,
        fail _ => false
    }

@[test]
def test_decls_fromlist_empty_sig_nl : Bool :=
    match class_parser "class FromListLiteral (L : Type -> Type := List) {\n  def empty : L A\n}\n" {
        success rem _ => true,
        fail _ => false
    }

@[test]
def test_is_space_newline : Bool :=
  is_space "\n"
