/// Lint levels and the precedence merge that decides one per diagnostic.
///
/// Precedence, highest wins (plans/implementations/linter.md):
///
///   1. `#[allow <rule>]` on the enclosing declaration -- NOT implemented in
///      this version, because the self-hosted lowering discards the `#[...]`
///      attributes on a `use`/`open` (`lower_parse_decl_kind` unwraps
///      `ParseDeclKind.attrs_d` to its inner declaration). That is a
///      `lang/src/parser/lower_parse.mo` change, not a linter one; until it
///      lands there is nowhere to put the suppression it would honour.
///   2. CLI: `--deny <rule>` / `--allow <rule>`, repeatable.
///   3. `mote.toml [lint]` -- not implemented in this version; see
///      `config_of_manifest` for what is missing.
///   4. The rule's own default level.
///
/// Levels gate EXIT CODES, and only `deny` does: `allow` suppresses
/// entirely, `warn` reports and never affects the exit code, `deny` reports
/// and fails. That matches the compiler's own warning semantics, where
/// `rust-cli/src/main.rs` exits on `error_count` alone.

use std::list {}

pub type LintLevel {
    allow,
    warn,
    deny,
}

/// `LintLevel` is three nullary tags, so a duplicate is a fresh tag -- the
/// "genuinely immutable value" remedy the affine rule names. Without it every
/// rule that consults a level while also holding one is a use-count
/// violation, which makes the rule unimplementable rather than merely
/// inconvenient.
pub instance Copy LintLevel {
    def copy (l : LintLevel) : Pair LintLevel LintLevel := Pair.pair l l
}

/// A rule name as the user spells it on the command line.
pub struct LintConfig {
    /// `--allow <rule>` names, from the CLI.
    allowed : List String,
    /// `--deny <rule>` names, from the CLI.
    denied : List String,
}

/// A `LintConfig` is two immutable `List String`s, both `Copy`, so a
/// field-wise duplicate is a value copy.
pub instance Copy LintConfig {
    def copy (c : LintConfig) : Pair LintConfig LintConfig :=
        match c {
            mk allowed denied =>
                let a : LintConfig := { allowed := allowed, denied := denied } in
                let b : LintConfig := { allowed := allowed, denied := denied } in
                Pair.pair a b,
        }
}

pub def LintConfig.empty : LintConfig :=
    let c : LintConfig := { allowed := List.empty, denied := List.empty } in
    c

pub def LintConfig.with_allowed (names : List String) (c : LintConfig) : LintConfig :=
    { c with allowed := List.append c.allowed names }

pub def LintConfig.with_denied (names : List String) (c : LintConfig) : LintConfig :=
    { c with denied := List.append c.denied names }

def lc_mem (x : String) (xs : List String) : Bool :=
    match xs {
        List.empty => false,
        List.cons y rest => String.beq x y || lc_mem x rest,
    }

/// The effective level for `rule`, given its `default` and the config.
///
/// `--deny` wins over `--allow` when a caller passes both for one rule: a
/// promotion asked for out loud is the more emphatic of the two, and the
/// alternative -- last-one-wins by argv order -- would make the flag's
/// meaning depend on a spelling the help text does not teach.
pub def effective_level (default : LintLevel) (config : LintConfig) (rule : String) : LintLevel :=
    if lc_mem rule config.denied then LintLevel.deny
    else if lc_mem rule config.allowed then LintLevel.allow
    else default

pub def level_name (l : LintLevel) : String :=
    match l {
        LintLevel.allow => "allow",
        LintLevel.warn => "warn",
        LintLevel.deny => "deny",
    }

/// Whether a level at or above `warn` reports anything at all.
pub def level_reports (l : LintLevel) : Bool :=
    match l {
        LintLevel.allow => false,
        LintLevel.warn => true,
        LintLevel.deny => true,
    }

/// Whether a level fails the run.
pub def level_fails (l : LintLevel) : Bool :=
    match l {
        LintLevel.allow => false,
        LintLevel.warn => false,
        LintLevel.deny => true,
    }

/// `LintLevel` as the number an editor's `severity` field wants. The values
/// are `toolkit::diagnostic`'s, restated here rather than imported: the
/// linter does not depend on `toolkit`, and these four numbers are fixed by
/// the LSP specification rather than by that module.
pub def level_severity (l : LintLevel) : I64 :=
    match l {
        LintLevel.allow => 4,
        LintLevel.warn => 2,
        LintLevel.deny => 1,
    }
