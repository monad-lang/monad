/// Smoke tests for the compiler's argv parser (`#[derive Cli]` in
/// `cli.mo`, decoded and exposed by `cli_spec.mo`).
///
/// `Command.from_args` is the old `Command`-returning facade: anything the
/// parser rejects becomes `Command.help`. The real entry point uses
/// `Command.run`, which keeps the error and the exit code; these tests pin
/// the decoded fields, which is where a flag rename or a positional-order
/// mistake shows up.
use lib::cli {*}
use lib::cli_spec {*}

def some_is (o : Option String) (want : String) : Bool :=
    match o {
        Option.some s => String.beq s want,
        Option.none => false,
    }

def is_none (o : Option String) : Bool :=
    match o {
        Option.some _ => false,
        Option.none => true,
    }

def one_string (xs : List String) (want : String) : Bool :=
    match xs {
        List.cons hd tl => String.beq hd want && List.is_empty tl,
        List.empty => false,
    }

def two_strings (xs : List String) (a : String) (b : String) : Bool :=
    match xs {
        List.cons x rest => String.beq x a && one_string rest b,
        List.empty => false,
    }

// ── build ──────────────────────────────────────────────────────────────

#[test]
def test_build_positional_name : Bool :=
    match Command.from_args ["build", "a.mo", "myname"] {
        Command.build file name _verbose debug release _no_cache _locked _target_dir _bin _target _offline output =>
            some_is file "a.mo" && some_is name "myname" && is_none output
                && debug == false && release == false,
        _ => false,
    }

#[test]
def test_build_default_name : Bool :=
    match Command.from_args ["build", "a.mo"] {
        Command.build file name _verbose _debug _release _no_cache _locked _target_dir _bin _target _offline output =>
            some_is file "a.mo" && is_none name && is_none output,
        _ => false,
    }

#[test]
def test_build_output_option_wins : Bool :=
    match Command.from_args ["build", "a.mo", "legacy", "--output", "out", "--verbose"] {
        Command.build _file _name verbose _debug _release _no_cache _locked _target_dir _bin _target _offline output =>
            some_is output "out" && verbose == true,
        _ => false,
    }

#[test]
def test_build_short_output_and_verbose : Bool :=
    match Command.from_args ["build", "a.mo", "-o", "out", "-v"] {
        Command.build _file _name verbose _debug _release _no_cache _locked _target_dir _bin _target _offline output =>
            some_is output "out" && verbose == true,
        _ => false,
    }

/// Debug info is ON by default; `--release` opts out and `--debug` opts back
/// in. `Command.debug_of` is the single place that rule lives.
#[test]
def test_build_debug_is_on_by_default : Bool :=
    Command.debug_of (Command.from_args ["build", "a.mo"]) == true

#[test]
def test_build_release_opts_out_of_debug : Bool :=
    Command.debug_of (Command.from_args ["build", "a.mo", "--release"]) == false

#[test]
def test_build_explicit_debug_beats_release : Bool :=
    Command.debug_of (Command.from_args ["build", "a.mo", "--release", "--debug"]) == true

#[test]
def test_build_short_debug_flag : Bool :=
    match Command.from_args ["build", "a.mo", "-g"] {
        Command.build _file _name _verbose debug _release _no_cache _locked _target_dir _bin _target _offline _output =>
            debug == true,
        _ => false,
    }

/// No positional path means the dispatch defaults to `.` (the mote
/// containing the working directory), matching check/test.
#[test]
def test_build_without_path : Bool :=
    match Command.from_args ["build"] {
        Command.build file _name _verbose _debug _release _no_cache _locked _target_dir _bin _target _offline _output =>
            is_none file,
        _ => false,
    }

#[test]
def test_build_no_cache_flag : Bool :=
    match Command.from_args ["build", "a.mo", "--no-cache"] {
        Command.build _file _name _verbose _debug _release no_cache _locked _target_dir _bin _target _offline _output =>
            no_cache == true,
        _ => false,
    }

#[test]
def test_build_bin_flag : Bool :=
    match Command.from_args ["build", "a.mo", "--bin", "tool"] {
        Command.build _file _name _verbose _debug _release _no_cache _locked _target_dir bin _target _offline _output =>
            some_is bin "tool",
        _ => false,
    }

#[test]
def test_build_target_flag : Bool :=
    match Command.from_args ["build", "a.mo", "--target", "aarch64-unknown-linux-gnu"] {
        Command.build _file _name _verbose _debug _release _no_cache _locked _target_dir _bin target _offline _output =>
            some_is target "aarch64-unknown-linux-gnu",
        _ => false,
    }

/// The clap parser accepts `--long=value`, which the old hand-written one
/// could not.
#[test]
def test_build_target_equals_form : Bool :=
    match Command.from_args ["build", "a.mo", "--target=aarch64-unknown-linux-gnu"] {
        Command.build _file _name _verbose _debug _release _no_cache _locked _target_dir _bin target _offline _output =>
            some_is target "aarch64-unknown-linux-gnu",
        _ => false,
    }

#[test]
def test_build_locked_and_target_dir : Bool :=
    match Command.from_args ["build", "a.mo", "--locked", "--target-dir", "t"] {
        Command.build _file _name _verbose _debug _release _no_cache locked target_dir _bin _target _offline _output =>
            locked == true && some_is target_dir "t",
        _ => false,
    }

/// `--offline` is accepted and ignored by build/check/test so one flag set
/// can drive a whole script.
#[test]
def test_build_accepts_offline : Bool :=
    match Command.from_args ["build", "a.mo", "--offline"] {
        Command.build _file _name _verbose _debug _release _no_cache _locked _target_dir _bin _target offline _output =>
            offline == true,
        _ => false,
    }

// ── install ────────────────────────────────────────────────────────────

#[test]
def test_install_mote : Bool :=
    match Command.from_args ["install", "motes/weaver"] {
        Command.install file output _bin _verbose _no_cache _target =>
            some_is file "motes/weaver" && is_none output,
        _ => false,
    }

#[test]
def test_install_default_path_is_cwd : Bool :=
    match Command.from_args ["install"] {
        Command.install file _output _bin _verbose _no_cache _target => is_none file,
        _ => false,
    }

#[test]
def test_install_output_and_flags : Bool :=
    match Command.from_args ["install", "a.mo", "-o", "tool", "--bin", "cli", "-v", "--no-cache", "--target", "aarch64-unknown-linux-gnu"] {
        Command.install file output bin verbose no_cache target =>
            some_is file "a.mo" && some_is output "tool" && some_is bin "cli"
                && verbose == true && no_cache == true
                && some_is target "aarch64-unknown-linux-gnu",
        _ => false,
    }

// ── run / eval / repl / pretty ─────────────────────────────────────────

#[test]
def test_run_forwards_program_args_after_separator : Bool :=
    match Command.from_args ["run", "a.mo", "--", "x", "-y"] {
        Command.run file args _verbose _debug _release =>
            String.beq file "a.mo" && two_strings args "x" "-y",
        _ => false,
    }

#[test]
def test_run_forwards_plain_args_too : Bool :=
    match Command.from_args ["run", "a.mo", "x"] {
        Command.run file args _verbose _debug _release =>
            String.beq file "a.mo" && one_string args "x",
        _ => false,
    }

#[test]
def test_run_debug_flags : Bool :=
    match Command.from_args ["run", "a.mo", "-v", "--release"] {
        Command.run _file _args verbose debug release =>
            verbose == true && debug == false && release == true,
        _ => false,
    }

#[test]
def test_eval_file_and_verbose : Bool :=
    match Command.from_args ["eval", "a.mo", "-v"] {
        Command.eval file verbose => String.beq file "a.mo" && verbose == true,
        _ => false,
    }

#[test]
def test_repl : Bool :=
    match Command.from_args ["repl"] {
        Command.repl => true,
        _ => false,
    }

#[test]
def test_pretty : Bool :=
    match Command.from_args ["pretty", "a.mo"] {
        Command.pretty file => String.beq file "a.mo",
        _ => false,
    }

// ── check / test ───────────────────────────────────────────────────────

#[test]
def test_check_files_and_flags : Bool :=
    match Command.from_args ["check", "a.mo", "b.mo", "-w", "--no-cache", "--locked", "--target-dir", "t", "--offline"] {
        Command.check files verbose workspace no_cache locked target_dir offline =>
            two_strings files "a.mo" "b.mo" && verbose == false && workspace == true
                && no_cache == true && locked == true && some_is target_dir "t"
                && offline == true,
        _ => false,
    }

#[test]
def test_check_bare_has_no_files : Bool :=
    match Command.from_args ["check"] {
        Command.check files _verbose _workspace _no_cache _locked _target_dir _offline =>
            List.is_empty files,
        _ => false,
    }

#[test]
def test_check_verbose : Bool :=
    match Command.from_args ["check", "-v"] {
        Command.check _files verbose _workspace _no_cache _locked _target_dir _offline =>
            verbose == true,
        _ => false,
    }

#[test]
def test_test_jobs_and_flags : Bool :=
    match Command.from_args ["test", "a.mo", "-j", "8", "--workspace", "--locked", "--offline"] {
        Command.test files _verbose workspace locked no_cache target_dir jobs offline =>
            one_string files "a.mo" && workspace == true && locked == true
                && no_cache == false && is_none target_dir
                && match jobs { Option.some n => n == 8, Option.none => false }
                && offline == true,
        _ => false,
    }

/// A non-numeric `--jobs` is rejected at parse time (the I64 validation the
/// `parsec` dependency used to do by hand), so the facade falls to help.
#[test]
def test_test_bad_jobs_is_a_usage_error : Bool :=
    match Command.from_args ["test", "-j", "many"] {
        Command.help => true,
        _ => false,
    }

// ── clean / gc / store / fetch ─────────────────────────────────────────

#[test]
def test_clean : Bool :=
    match Command.from_args ["clean", "--all", "--target-dir", "t"] {
        Command.clean all target_dir => all == true && some_is target_dir "t",
        _ => false,
    }

#[test]
def test_gc : Bool :=
    match Command.from_args ["gc", "a.mo", "-w", "--apply"] {
        Command.gc files workspace apply target_dir =>
            one_string files "a.mo" && workspace == true && apply == true && is_none target_dir,
        _ => false,
    }

#[test]
def test_store : Bool :=
    match Command.from_args ["store", "verify"] {
        Command.store sub _target_dir => String.beq sub "verify",
        _ => false,
    }

#[test]
def test_fetch_and_update : Bool :=
    match Command.from_args ["fetch", "some/dir", "--offline"] {
        Command.fetch dir offline => some_is dir "some/dir" && offline == true,
        _ => false,
    }

#[test]
def test_update_defaults_to_cwd : Bool :=
    match Command.from_args ["update"] {
        Command.update dir offline => is_none dir && offline == false,
        _ => false,
    }

// ── simple verbs and the fallback ──────────────────────────────────────

#[test]
def test_print_targets : Bool :=
    match Command.from_args ["print-targets"] {
        Command.print_targets => true,
        _ => false,
    }

#[test]
def test_lsp_and_version : Bool :=
    match Command.from_args ["lsp"] {
        Command.lsp => match Command.from_args ["version"] {
            Command.version => true,
            _ => false,
        },
        _ => false,
    }

/// Unknown words, an empty argv, and `--help` all fall to the help screen in
/// the facade. (`Command.run` keeps the distinction: `--help` prints to
/// stdout and exits 0, a usage error prints to stderr and exits 2.)
#[test]
def test_unknown_and_help_fall_to_help : Bool :=
    match Command.from_args ["compile", "a.mo"] {
        Command.help => match Command.from_args [] {
            Command.help => match Command.from_args ["--help"] {
                Command.help => true,
                _ => false,
            },
            _ => false,
        },
        _ => false,
    }
