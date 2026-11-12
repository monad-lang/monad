/// The high-level IR: the AST with every flag resolved, every class a
/// range set, and every literal a one-scalar class. Nothing downstream of
/// `translate` knows about flags.
use lib::error {RegexSpan, RegexSpan.at, RegexError}
use lib::syntax::ast {
    RxAst, RxAssert, RxClassItem, RxClassSet, RxFlag, RxFlagItem, RxGroupKind, RxPerl, RxSetOp,
}
use lib::charclass {
    max_scalar, max_byte, class_of_list, class_union, class_negate, class_intersect,
    class_difference, class_symmetric_difference, class_case_fold,
}
use unicode::lookup {
    Unicode.gc_ranges, Unicode.script_ranges, Unicode.white_space_ranges, Unicode.word_ranges,
    Unicode.digit_ranges, Unicode.simple_fold_entries, Unicode.normalize_name,
}
use std::list {List.any, List.filter}

/// A zero-width assertion, resolved.
pub type RxLook {
    start_text,
    end_text,
    /// Start of a line (`^` under `m`).
    start_line,
    /// End of a line (`$` under `m`).
    end_line,
    word_unicode,
    not_word_unicode,
    word_ascii,
    not_word_ascii,
}

pub type RxHir {
    empty,
    /// A set of scalar values matched as UTF-8 (`bytes` false), or of raw
    /// bytes (`bytes` true, under `(?-u)`).
    cset (ranges : List (Pair I64 I64)) (bytes : Bool),
    look (kind : RxLook),
    repetition (min : I64) (max : Option I64) (greedy : Bool) (sub : RxHir),
    /// A capture group with its 1-based index.
    capture (index : I64) (sub : RxHir),
    concat (items : List RxHir),
    alternation (items : List RxHir),
}

/// The flags in force at a point of the pattern.
pub struct RxFlags {
    case_insensitive : Bool,
    multi_line : Bool,
    dot_matches_new_line : Bool,
    swap_greed : Bool,
    unicode : Bool,
}

/// What every translation step can see: the simple case-fold orbits, decoded
/// once and only when some part of the pattern is case-insensitive.
struct RxCtx {
    fold : List (Pair I64 (List I64)),
}

type RxT {
    t_ok (hir : RxHir) (flags : RxFlags),
    t_fail (e : RegexError),
}

pub def translate (ast : RxAst) (flags : RxFlags) : Result RegexError RxHir :=
    let ctx : RxCtx := {
        fold := if flags.case_insensitive || wants_fold ast then Unicode.simple_fold_entries else List.empty,
    } in
    match translate_ast ast flags ctx {
        RxT.t_ok h _ => Result.ok h,
        RxT.t_fail e => Result.err e,
    }

// ─── Flags ───

#[terminating]
def wants_fold (a : RxAst) : Bool :=
    match a {
        RxAst.set_flags _ items => sets_i items,
        RxAst.group _ kind sub =>
            match kind {
                RxGroupKind.non_capture items => sets_i items || wants_fold sub,
                _ => wants_fold sub,
            },
        RxAst.repetition _ _ _ _ sub => wants_fold sub,
        RxAst.concat _ items => List.any wants_fold items,
        RxAst.alternation _ items => List.any wants_fold items,
        _ => false,
    }

#[terminating]
def sets_i (items : List RxFlagItem) : Bool :=
    match items {
        List.empty => false,
        List.cons it rest =>
            match it.flag {
                RxFlag.case_insensitive => it.on || sets_i rest,
                _ => sets_i rest,
            },
    }

def apply_flag (f : RxFlags) (it : RxFlagItem) : RxFlags :=
    match it.flag {
        RxFlag.case_insensitive => { f with case_insensitive := it.on },
        RxFlag.multi_line => { f with multi_line := it.on },
        RxFlag.dot_matches_new_line => { f with dot_matches_new_line := it.on },
        RxFlag.swap_greed => { f with swap_greed := it.on },
        RxFlag.ignore_whitespace => f,
        RxFlag.unicode => { f with unicode := it.on },
    }

#[terminating]
def apply_flags (f : RxFlags) (items : List RxFlagItem) : RxFlags :=
    match items {
        List.empty => f,
        List.cons it rest => apply_flags (apply_flag f it) rest,
    }

// ─── Translation ───

def fail_at (msg : String) (sp : RegexSpan) : RxT := RxT.t_fail (RegexError.syntax msg sp)

#[terminating]
def translate_ast (a : RxAst) (f : RxFlags) (ctx : RxCtx) : RxT :=
    match a {
        RxAst.empty _ => RxT.t_ok RxHir.empty f,
        RxAst.literal _ cp => RxT.t_ok (literal_hir cp f ctx) f,
        RxAst.dot _ => RxT.t_ok (dot_hir f) f,
        RxAst.assertion _ k => RxT.t_ok (RxHir.look (assert_look k f)) f,
        RxAst.perl _ k negated => RxT.t_ok (class_hir (perl_ranges k f.unicode) negated f ctx) f,
        RxAst.unicode_class sp name negated => unicode_hir sp name negated f ctx,
        RxAst.bracket sp negated set =>
            match set_ranges set f sp {
                Result.ok rs => RxT.t_ok (class_hir rs negated f ctx) f,
                Result.err e => RxT.t_fail e,
            },
        RxAst.repetition _ min max greedy sub => repetition_hir min max greedy sub f ctx,
        RxAst.group _ kind sub => group_hir kind sub f ctx,
        RxAst.set_flags _ items => RxT.t_ok RxHir.empty (apply_flags f items),
        RxAst.concat _ items => seq_hir items f ctx List.empty false,
        RxAst.alternation _ items => seq_hir items f ctx List.empty true,
    }

#[terminating]
def repetition_hir (min : I64) (max : Option I64) (greedy : Bool) (sub : RxAst) (f : RxFlags) (ctx : RxCtx) : RxT :=
    match translate_ast sub f ctx {
        RxT.t_ok h _ => RxT.t_ok (RxHir.repetition min max (Bool.not (I64.beq (bool_bit greedy) (bool_bit f.swap_greed))) h) f,
        RxT.t_fail e => RxT.t_fail e,
    }

def bool_bit (b : Bool) : I64 := if b then 1 else 0

/// A group's flags end with it: the enclosing flags come back unchanged.
#[terminating]
def group_hir (kind : RxGroupKind) (sub : RxAst) (f : RxFlags) (ctx : RxCtx) : RxT :=
    match kind {
        RxGroupKind.capture idx => capture_hir idx sub f ctx,
        RxGroupKind.named _ idx => capture_hir idx sub f ctx,
        RxGroupKind.non_capture items =>
            match translate_ast sub (apply_flags f items) ctx {
                RxT.t_ok h _ => RxT.t_ok h f,
                RxT.t_fail e => RxT.t_fail e,
            },
    }

#[terminating]
def capture_hir (idx : I64) (sub : RxAst) (f : RxFlags) (ctx : RxCtx) : RxT :=
    match translate_ast sub f ctx {
        RxT.t_ok h _ => RxT.t_ok (RxHir.capture idx h) f,
        RxT.t_fail e => RxT.t_fail e,
    }

/// A concatenation or an alternation, items left to right: a standalone
/// `(?flags)` changes the flags for every later item, across `|` too, up to
/// the end of the enclosing group.
#[terminating]
def seq_hir (items : List RxAst) (f : RxFlags) (ctx : RxCtx) (acc : List RxHir) (is_alt : Bool) : RxT :=
    match items {
        List.empty =>
            let hs : List RxHir := List.reverse acc in
            RxT.t_ok (if is_alt then RxHir.alternation hs else RxHir.concat (List.filter not_empty hs)) f,
        List.cons it rest =>
            match translate_ast it f ctx {
                RxT.t_ok h f2 => seq_hir rest f2 ctx (List.cons h acc) is_alt,
                RxT.t_fail e => RxT.t_fail e,
            },
    }

def not_empty (h : RxHir) : Bool :=
    match h {
        RxHir.empty => false,
        _ => true,
    }

// ─── Leaves ───

def universe (f : RxFlags) : I64 := if f.unicode then max_scalar else max_byte

/// Fold (when `i` is on) before negating, as Rust's `regex` does:
/// `(?i)[^a]` excludes both `a` and `A`. Without `u`, folding is ASCII-only.
def class_hir (rs : List (Pair I64 I64)) (negated : Bool) (f : RxFlags) (ctx : RxCtx) : RxHir :=
    let folded : List (Pair I64 I64) := if f.case_insensitive then fold_class rs f ctx else rs in
    let final : List (Pair I64 I64) := if negated then class_negate folded (universe f) else folded in
    RxHir.cset final (Bool.not f.unicode)

def fold_class (rs : List (Pair I64 I64)) (f : RxFlags) (ctx : RxCtx) : List (Pair I64 I64) :=
    if f.unicode then class_case_fold rs ctx.fold
    else class_union rs (class_intersect (class_case_fold rs ctx.fold) [Pair.pair 0 127])

/// Under `(?-u)` a literal up to 0xFF is a byte (`\xFF` matches the byte
/// 0xFF); a wider one still matches its UTF-8 encoding.
def literal_hir (cp : I64) (f : RxFlags) (ctx : RxCtx) : RxHir :=
    let rs : List (Pair I64 I64) := [Pair.pair cp cp] in
    let folded : List (Pair I64 I64) := if f.case_insensitive then fold_class rs f ctx else rs in
    RxHir.cset folded (Bool.not f.unicode && I64.lt cp 256)

def dot_hir (f : RxFlags) : RxHir :=
    let top : I64 := universe f in
    if f.dot_matches_new_line then RxHir.cset [Pair.pair 0 top] (Bool.not f.unicode)
    else RxHir.cset [Pair.pair 0 9, Pair.pair 11 top] (Bool.not f.unicode)

def assert_look (k : RxAssert) (f : RxFlags) : RxLook :=
    match k {
        RxAssert.start_line => if f.multi_line then RxLook.start_line else RxLook.start_text,
        RxAssert.end_line => if f.multi_line then RxLook.end_line else RxLook.end_text,
        RxAssert.start_text => RxLook.start_text,
        RxAssert.end_text => RxLook.end_text,
        RxAssert.word_boundary => if f.unicode then RxLook.word_unicode else RxLook.word_ascii,
        RxAssert.not_word_boundary => if f.unicode then RxLook.not_word_unicode else RxLook.not_word_ascii,
    }

pub def ascii_word : List (Pair I64 I64) :=
    [Pair.pair 48 57, Pair.pair 65 90, Pair.pair 95 95, Pair.pair 97 122]

def perl_ranges (k : RxPerl) (u : Bool) : List (Pair I64 I64) :=
    match k {
        RxPerl.digit => if u then Unicode.digit_ranges else [Pair.pair 48 57],
        RxPerl.space => if u then Unicode.white_space_ranges else [Pair.pair 9 13, Pair.pair 32 32],
        RxPerl.word => if u then Unicode.word_ranges else ascii_word,
    }

def perl_class (k : RxPerl) (negated : Bool) (f : RxFlags) : List (Pair I64 I64) :=
    let rs : List (Pair I64 I64) := perl_ranges k f.unicode in
    if negated then class_negate rs (universe f) else rs

def ascii_class (name : String) : List (Pair I64 I64) :=
    if String.beq name "alnum" then [Pair.pair 48 57, Pair.pair 65 90, Pair.pair 97 122]
    else if String.beq name "alpha" then [Pair.pair 65 90, Pair.pair 97 122]
    else if String.beq name "ascii" then [Pair.pair 0 127]
    else if String.beq name "blank" then [Pair.pair 9 9, Pair.pair 32 32]
    else if String.beq name "cntrl" then [Pair.pair 0 31, Pair.pair 127 127]
    else if String.beq name "digit" then [Pair.pair 48 57]
    else if String.beq name "graph" then [Pair.pair 33 126]
    else if String.beq name "lower" then [Pair.pair 97 122]
    else if String.beq name "print" then [Pair.pair 32 126]
    else if String.beq name "punct" then [Pair.pair 33 47, Pair.pair 58 64, Pair.pair 91 96, Pair.pair 123 126]
    else if String.beq name "space" then [Pair.pair 9 13, Pair.pair 32 32]
    else if String.beq name "upper" then [Pair.pair 65 90]
    else if String.beq name "word" then ascii_word
    else [Pair.pair 48 57, Pair.pair 65 70, Pair.pair 97 102]

// ─── Unicode properties ───

def unicode_hir (sp : RegexSpan) (name : String) (negated : Bool) (f : RxFlags) (ctx : RxCtx) : RxT :=
    if Bool.not f.unicode then fail_at "Unicode classes are not allowed when the u flag is off" sp
    else match prop_ranges name {
        Option.some rs => RxT.t_ok (class_hir rs negated f ctx) f,
        Option.none => fail_at "unrecognized Unicode class name" sp,
    }

/// `Any`, `ASCII`, `Assigned`, a General_Category or Script name, or
/// `gc=`/`sc=` (also `general_category=`, `script=`, with `:` for `=`).
pub def prop_ranges (name : String) : Option (List (Pair I64 I64)) :=
    match split_key name {
        Option.some kv => keyed_prop (Unicode.normalize_name kv.first) kv.second,
        Option.none => bare_prop name,
    }

def keyed_prop (key : String) (value : String) : Option (List (Pair I64 I64)) :=
    if String.beq key "gc" || String.beq key "generalcategory" then Unicode.gc_ranges value
    else if String.beq key "sc" || String.beq key "script" then Unicode.script_ranges value
    else Option.none

def bare_prop (name : String) : Option (List (Pair I64 I64)) :=
    let n : String := Unicode.normalize_name name in
    if String.beq n "any" then Option.some [Pair.pair 0 max_scalar]
    else if String.beq n "ascii" then Option.some [Pair.pair 0 127]
    else if String.beq n "assigned" then
        match Unicode.gc_ranges "Cn" {
            Option.some cn => Option.some (class_negate cn max_scalar),
            Option.none => Option.none,
        }
    else match Unicode.gc_ranges name {
        Option.some rs => Option.some rs,
        Option.none => Unicode.script_ranges name,
    }

def split_key (name : String) : Option (Pair String String) :=
    match String.index_of name "=" {
        Option.some i => Option.some (cut name i),
        Option.none =>
            match String.index_of name ":" {
                Option.some i => Option.some (cut name i),
                Option.none => Option.none,
            },
    }

def cut (s : String) (i : I64) : Pair String String :=
    Pair.pair (String.slice s 0 i) (String.slice s (i + 1) (String.length s - i - 1))

// ─── Bracketed classes ───

#[terminating]
def set_ranges (set : RxClassSet) (f : RxFlags) (sp : RegexSpan) : Result RegexError (List (Pair I64 I64)) :=
    match set {
        RxClassSet.items list => items_ranges list f sp List.empty,
        RxClassSet.op kind lhs rhs =>
            match set_ranges lhs f sp {
                Result.err e => Result.err e,
                Result.ok l => op_rhs kind l rhs f sp,
            },
    }

#[terminating]
def op_rhs (kind : RxSetOp) (l : List (Pair I64 I64)) (rhs : RxClassSet) (f : RxFlags) (sp : RegexSpan) : Result RegexError (List (Pair I64 I64)) :=
    match set_ranges rhs f sp {
        Result.err e => Result.err e,
        Result.ok r => Result.ok (apply_op kind l r),
    }

def apply_op (kind : RxSetOp) (l : List (Pair I64 I64)) (r : List (Pair I64 I64)) : List (Pair I64 I64) :=
    match kind {
        RxSetOp.intersection => class_intersect l r,
        RxSetOp.difference => class_difference l r,
        RxSetOp.symmetric_difference => class_symmetric_difference l r,
    }

#[terminating]
def items_ranges (items : List RxClassItem) (f : RxFlags) (sp : RegexSpan) (acc : List (Pair I64 I64)) : Result RegexError (List (Pair I64 I64)) :=
    match items {
        List.empty => Result.ok (class_of_list acc),
        List.cons it rest =>
            match item_ranges it f sp {
                Result.err e => Result.err e,
                Result.ok rs => items_ranges rest f sp (List.append rs acc),
            },
    }

#[terminating]
def item_ranges (it : RxClassItem) (f : RxFlags) (sp : RegexSpan) : Result RegexError (List (Pair I64 I64)) :=
    match it {
        RxClassItem.lit cp => Result.ok [Pair.pair cp cp],
        RxClassItem.range lo hi => Result.ok [Pair.pair lo hi],
        RxClassItem.ascii name negated =>
            Result.ok (if negated then class_negate (ascii_class name) (universe f) else ascii_class name),
        RxClassItem.perl kind negated => Result.ok (perl_class kind negated f),
        RxClassItem.unicode name negated =>
            if Bool.not f.unicode then Result.err (RegexError.syntax "Unicode classes are not allowed when the u flag is off" sp)
            else match prop_ranges name {
                Option.some rs => Result.ok (if negated then class_negate rs max_scalar else rs),
                Option.none => Result.err (RegexError.syntax "unrecognized Unicode class name" sp),
            },
        RxClassItem.bracket negated set =>
            match set_ranges set f sp {
                Result.err e => Result.err e,
                Result.ok rs => Result.ok (if negated then class_negate rs (universe f) else rs),
            },
    }
