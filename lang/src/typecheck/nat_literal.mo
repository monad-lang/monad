/// Nat literals: the canonical unary chain a small `Nat` literal denotes,
/// and the two directions the checker needs.
///
/// A literal used at a `Nat` position is rewritten by `infer.mo`'s
/// `apply_nat_rewrite` to `Nat.of_i64 <lit>` (`n <= 64`) or to a unary
/// `Nat.succ` chain (`n > 64`). `Nat.of_i64`'s body calls the native
/// `I64.lt`, so it cannot reduce by delta alone; `whnf.mo` therefore uses
/// `nat_of_i64_unary_app` to reduce a literal-indexed application to the
/// same chain. That is what lets `Nat.sub`/`Nat.add` on literal indices
/// reduce, which is what `Slice`'s `split` types depend on.
///
/// This module is separate from `ctor_refine.mo` and `whnf.mo` on purpose:
/// `whnf` must not import `ctor_refine` (which uses the reduction), and
/// `nat_value_of` must not import `whnf` (the obligation check reduces
/// first, then asks for the value).
use lib::types {
    DebugName, Identifier, Literal, Term, sentinel, show_identifier, term_peel,
}

/// The largest `Nat` literal unfolded to a constructor chain (`whnf`'s
/// bound; `infer.mo`'s rewrite uses the same number).
pub def nat_literal_bound : I64 := 64

/// A small `Nat` literal as its canonical unary constructor chain. `Vec 3`
/// must compare with `Vec (succ (succ (succ zero)))`; the chain's heads are
/// sentinel variables named `Nat.zero`/`Nat.succ`, which `whnf_con_head`
/// recognises by simple name, so iota fires on them like on a `Term.con`.
#[partial]
pub def nat_literal_term (n : I64) : Term :=
    if I64.beq n 0 then
        Term.var sentinel (DebugName.named (Identifier.id "Nat.zero"))
    else
        Term.app (Term.var sentinel (DebugName.named (Identifier.id "Nat.succ")))
            (nat_literal_term (I64.sub n 1))

/// `t` as a constructor chain when it is a small non-negative integer literal
/// or `Nat.of_i64` of one; otherwise `t` unchanged.
pub def nat_literal_unary (t : Term) : Term :=
    match small_nat_literal t {
        Option.some n => nat_literal_term n,
        Option.none => t,
    }

/// `nat_literal_unary` through a constructor chain: `succ 0` is `succ zero`.
#[terminating]
pub def nat_literal_deep (t : Term) : Term :=
    match small_nat_literal t {
        Option.some n => nat_literal_term n,
        Option.none =>
            match term_peel t {
                Term.app f a => Term.app f (nat_literal_deep a),
                _ => t,
            },
    }

/// `t` as an `I64` when it is a small integer literal, `Nat.of_i64` of one,
/// or a `Nat` constructor chain.
#[terminating]
pub def small_nat_literal (t : Term) : Option I64 :=
    match term_peel t {
        Term.lit l =>
            match l {
                Literal.num n _ =>
                    if I64.lt n 0 || I64.lt nat_literal_bound n
                    then Option.none
                    else Option.some n,
                _ => Option.none,
            },
        _ =>
            match of_i64_app t {
                Option.some arg => small_nat_literal arg,
                Option.none => Option.none,
            },
    }

/// `Nat.of_i64 <arg>` -- the builder application `apply_nat_rewrite` emits
/// for a literal at a `Nat` position -- peeled of `ctx`. The name may be
/// the bare spelling the rewrite falls back to or a resolved path whose
/// tail is `Nat.of_i64`.
def of_i64_app (t : Term) : Option Term :=
    match term_peel t {
        Term.app f a =>
            match term_peel f {
                Term.var idx dbg =>
                    if I64.beq idx sentinel then
                        match dbg {
                            DebugName.named id =>
                                if is_nat_of_i64_name (show_identifier id)
                                then Option.some a
                                else Option.none,
                            DebugName.unnamed => Option.none,
                        }
                    else Option.none,
                _ => Option.none,
            },
        _ => Option.none,
    }

def is_nat_of_i64_name (s : String) : Bool :=
    String.beq s "Nat.of_i64"
        || String.ends_with s "::Nat.of_i64"
        || String.ends_with s ".Nat.of_i64"

/// The unary chain a literal-indexed `Nat.of_i64` application denotes,
/// when its argument is a small literal. This is `whnf.mo`'s reduction
/// step for the builder.
pub def nat_of_i64_unary_app (t : Term) : Option Term :=
    match of_i64_app t {
        Option.some arg =>
            match small_nat_literal arg {
                Option.some n => Option.some (nat_literal_term n),
                Option.none => Option.none,
            },
        Option.none => Option.none,
    }

/// A `Nat` term as an `I64`: a literal, `Nat.of_i64 <lit>`, or a
/// `zero`/`succ` chain (the shapes `nat_literal_term` builds and `whnf`
/// produces). The CALLER reduces first (this module must not import
/// `whnf`); the chain is all this needs to count.
#[terminating]
pub def nat_value_of (t : Term) : Option I64 :=
    match term_peel t {
        Term.lit l =>
            match l {
                Literal.num n _ => Option.some n,
                _ => Option.none,
            },
        Term.var _idx dbg =>
            match dbg {
                DebugName.named id =>
                    if is_nat_ctor_name (show_identifier id) "zero"
                    then Option.some 0
                    else Option.none,
                DebugName.unnamed => Option.none,
            },
        Term.app f a =>
            match of_i64_app t {
                Option.some arg => nat_value_of arg,
                Option.none =>
                    match chain_head_name f {
                        Option.some id =>
                            if is_nat_ctor_name id "succ"
                            then
                                match nat_value_of a {
                                    Option.some n => Option.some (I64.add n 1),
                                    Option.none => Option.none,
                                }
                            else Option.none,
                        Option.none => Option.none,
                    },
            },
        _ => Option.none,
    }

/// The simple name a constructor-application head spells, peeled of `ctx`.
def chain_head_name (t : Term) : Option String :=
    match term_peel t {
        Term.var _idx dbg =>
            match dbg {
                DebugName.named id => Option.some (show_identifier id),
                DebugName.unnamed => Option.none,
            },
        _ => Option.none,
    }

/// `name` is `Nat`'s constructor `ctor` (`zero` / `succ`), bare, dotted, or
/// module-qualified -- never another type's same-named constructor.
def is_nat_ctor_name (name : String) (ctor : String) : Bool :=
    let qualified : String := String.concat "Nat." ctor in
    String.beq name qualified
        || String.ends_with name (String.concat "." qualified)
        || String.ends_with name (String.concat "::" qualified)
