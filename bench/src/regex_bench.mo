/// The regex mote's workloads (plans/library-ideas/regex.md, §Testing):
/// a literal search, an email-shaped pattern, `find_all` of `\d+`, date
/// captures and a 100-keyword union, each over a 256 KiB haystack.
///
/// Public API only, so the same file measures any revision of the mote
/// (the Pike-VM-only numbers come from running it before Phase 5).
/// Gated on MONAD_BENCH=1, as `regex_spike.mo` is.
///
/// ```text
/// MONAD_BENCH=1 monad test bench/src/regex_bench.mo
/// ```
use std::bench {Bench.now}
use regex::regex {Regex, Regex.new, Regex.find, Regex.find_all, Regex.captures_all, Match, Captures}
use std::list {List.intercalate}
open IO {get_env, println}

def bench_enabled : IO Bool := do {
    let v <- get_env "MONAD_BENCH";
    return (match v { Option.some _ => true, Option.none => false })
}

/// `s` doubled `k` times (`String.repeat` concatenates one copy at a time).
#[terminating]
def doubled (s : String) (k : I64) : String :=
    if I64.lt 0 k then doubled (String.concat s s) (k - 1) else s

/// 64-byte log lines, 4096 of them: 256 KiB.
def line : String := "2026-11-12 host-7 user42 ok from mail alice@example.com code 913\n"

def haystack : String := doubled line 12

def keywords : List String := [
    "abstract", "assert", "boolean", "break", "byte", "case", "catch", "char", "const", "continue",
    "default", "double", "else", "enum", "extends", "final", "finally", "float", "for", "goto",
    "implements", "import", "instanceof", "int", "interface", "long", "native", "new", "package",
    "private", "protected", "public", "return", "short", "static", "strictfp", "super", "switch",
    "synchronized", "this", "throw", "throws", "transient", "try", "void", "volatile", "while",
    "async", "await", "yield", "match", "where", "trait", "impl", "struct", "union", "unsafe",
    "crate", "extern", "loop", "move", "mut", "pub", "ref", "self", "type", "use", "virtual",
    "sizeof", "typeof", "alignof", "offsetof", "macro", "module", "export", "inline", "register",
    "signed", "unsigned", "template", "typename", "namespace", "operator", "friend", "mutable",
    "explicit", "delete", "noexcept", "nullptr", "decltype", "constexpr", "thread", "local",
    "concept", "requires", "consteval", "constinit", "zebra",
]

/// `what` names `n`: a result count, or a match position.
def report (label : String) (ms : I64) (what : String) (n : I64) : IO Unit :=
    println (String.concat_list [label, ": ", I64.to_string ms, " ms (", what, " ", I64.to_string n, ")"])

def time_find_all (label : String) (pat : String) (hay : String) : IO Unit := do {
    let t0 <- Bench.now;
    let n : I64 := match Regex.new pat { Result.ok r => List.length (Regex.find_all r hay), Result.err _ => 0 - 1 };
    let t1 <- Bench.now;
    report label (t1 - t0) "results" n
}

def time_find (label : String) (pat : String) (hay : String) : IO Unit := do {
    let t0 <- Bench.now;
    let n : I64 := match Regex.new pat {
        Result.ok r => (match Regex.find r hay { Option.some m => m.start, Option.none => 0 - 1 }),
        Result.err _ => 0 - 2,
    };
    let t1 <- Bench.now;
    report label (t1 - t0) "match at" n
}

def time_captures (label : String) (pat : String) (hay : String) : IO Unit := do {
    let t0 <- Bench.now;
    let n : I64 := match Regex.new pat { Result.ok r => List.length (Regex.captures_all r hay), Result.err _ => 0 - 1 };
    let t1 <- Bench.now;
    report label (t1 - t0) "results" n
}

#[test]
def bench_regex : IO Bool := do {
    let on <- bench_enabled;
    if Bool.not on then return true
    else do {
        let hay : String := haystack;
        let tail : String := String.concat hay "the needle Sherlock is here";
        println (String.concat_list ["haystack: ", I64.to_string (String.length hay), " bytes"]);
        time_find "literal find (end of text)" "Sherlock" tail;
        time_find_all r#"find_all \w+@\w+\.\w+"# r#"\w+@\w+\.\w+"# hay;
        time_find_all r#"find_all \d+"# r#"\d+"# hay;
        time_captures "captures_all date" r#"(\d{4})-(\d{2})-(\d{2})"# hay;
        time_find_all "find_all 100-keyword union" (List.intercalate "|" keywords) hay;
        return true
    }
}
