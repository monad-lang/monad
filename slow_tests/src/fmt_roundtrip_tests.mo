/// The whole-corpus formatter gate.
///
/// For every `.mo` in the compiler corpus:
///
/// 1. `Fmt.format_source` must succeed. The library re-lexes its own output
///    and requires the token stream (kind + verbatim text) and every
///    parser-sensitive tight pair to be unchanged; a failure here means the
///    lexer/renderer pair is wrong.
/// 2. The input and the formatted output must both pass the STRICT parser, so
///    the output is real Monad, not merely lexically similar.
/// 3. `show_decls` of the two parses must be equal. This is a secondary check:
///    `show_decls` omits attributes and def constraints (`lang/src/pretty.mo`),
///    so it cannot see everything; the token gate covers the bytes.
/// 4. Formatting is idempotent.
///
/// Any lexical construct the tokenizer mishandles shows up here, which is the
/// intended drift alarm between this mirror and the compiler's grammar.

use std::list {List.length}
open IO {println, read_file}
use lang::module {expand_check_paths, try_parse_decls_strict}
use lang::pretty {show_decls}
use fmt::fmt {Fmt.default_config, Fmt.format_source}

/// The compiler corpus. Kept as explicit roots rather than the whole repo so
/// an unrelated `.mo` fixture with intentionally invalid syntax (if one ever
/// appears) does not turn this gate red for the wrong reason.
def corpus_roots : List String :=
    ["init", "std", "lang", "cli", "llvm", "runtime", "build", "eval", "motes", "examples"]

def decls_render (src : String) (path : String) : Option String :=
    match try_parse_decls_strict src (Option.some path) {
        Result.ok decls => Option.some (show_decls decls),
        Result.err _ => Option.none,
    }

def same_decls (a : String) (b : String) (path : String) : Bool :=
    match decls_render a path {
        Option.none => false,
        Option.some shown_a => match decls_render b path {
            Option.none => false,
            Option.some shown_b => String.beq shown_a shown_b,
        },
    }

def idempotent (src : String) : Bool :=
    match Fmt.format_source Fmt.default_config src {
        Result.err _ => false,
        Result.ok once => match Fmt.format_source Fmt.default_config once {
            Result.err _ => false,
            Result.ok twice => String.beq once twice,
        },
    }

def corpus_file_ok (path : String) (src : String) : Bool :=
    match Fmt.format_source Fmt.default_config src {
        Result.err _ => false,
        Result.ok out =>
            same_decls src out path &&
            idempotent src,
    }

def check_corpus_file (path : String) : IO Bool := do {
    let r <- read_file (Path.path path);
    match r {
        Result.err _ => do {
            println ("fmt corpus: cannot read " ++ path);
            return false
        },
        Result.ok src => do {
            let ok : Bool := corpus_file_ok path src;
            if ok then return true
            else do {
                // Re-run just enough to say WHY, without failing the rest of
                // the corpus silently.
                match Fmt.format_source Fmt.default_config src {
                    Result.err e => println ("fmt corpus: " ++ path ++ " (byte " ++
                        I64.to_string e.offset ++ "): " ++ e.message),
                    Result.ok _ => println ("fmt corpus: " ++ path ++
                        ": parse, structure, or idempotence check failed"),
                };
                return false
            }
        },
    }
}

/// Keep going after a failure so one run reports every bad file, not just the
/// first; the expensive formatting happens either way.
#[partial]
def corpus_loop (files : List String) (ok : Bool) : IO Bool := do {
    match files {
        List.empty => return ok,
        List.cons path rest => do {
            let this_ok <- check_corpus_file path;
            corpus_loop rest (ok && this_ok)
        },
    }
}

#[test]
def test_corpus_roundtrip : IO Bool := do {
    let files <- expand_check_paths corpus_roots;
    println ("fmt corpus: " ++ I64.to_string (List.length files) ++ " file(s)");
    corpus_loop files true
}
