/// Module loading infrastructure for the self-hosted compiler.
/// Parses source text and builds scope data from declarations.

use lang.types
use lang.parser
use lang.scope

open types
open parser
open scope

/// Parse all declarations from source text.
/// Repeatedly consumes whitespace and parses one declaration,
/// accumulating into a List Decl. Stops when no more declarations
/// can be parsed.
@[partial]
def parse_all_decls (input : String) : ParseResult (List Decl) :=
    let decl_parser : (String -> ParseResult Decl) := fn s => t2_decl_parser (skip_spaces s) in
    many0 decl_parser input

/// Parse source text and build scope data for a module.
/// Does not resolve `use` dependencies — only parses and builds
/// scope for the declarations in the given text.
@[partial]
def parse_module (path : ModulePath) (text : String) : ScopeData :=
    let empty_decls : List Decl := List.empty in
    match parse_all_decls text {
        success _ decls => build_scope_from_decls path decls,
        fail _ => build_scope_from_decls path empty_decls
    }
