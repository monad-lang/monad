/// `moon static` argument parsing. No sockets: `Server.serve_static` never
/// returns, and `static_tests.mo` already covers the file handler it wraps.
use clap::parse {Cli.parse}
use clap::spec {Cli.ParseResult, Cli.Parsed}
use lib::static_cli {StaticCli, StaticCli.decode, StaticCli.parse_port}

def ok_parsed (r : Cli.ParseResult) : Option Cli.Parsed :=
    match r {
        Cli.ParseResult.parse_ok p => Option.some p,
        _ => Option.none,
    }

def decoded (args : List String) : Option StaticCli :=
    match ok_parsed (Cli.parse StaticCli.spec args) {
        Option.none => Option.none,
        Option.some p =>
            match StaticCli.decode p {
                Result.ok c => Option.some c,
                Result.err _ => Option.none,
            },
    }

def is_port (expected : U16) (s : String) : Bool :=
    match StaticCli.parse_port s {
        Option.some p => U16.beq p expected,
        Option.none => false,
    }

def rejects_port (s : String) : Bool :=
    match StaticCli.parse_port s {
        Option.some _ => false,
        Option.none => true,
    }

#[test]
def test_parse_port_accepts_valid : Bool :=
    is_port 1u16 "1" && is_port 8000u16 "8000" && is_port 65535u16 "65535"

#[test]
def test_parse_port_rejects_junk : Bool :=
    rejects_port "0" && rejects_port "65536" && rejects_port "" && rejects_port "80x" && rejects_port "-1"

#[test]
def test_static_defaults : Bool :=
    match decoded ["static"] {
        Option.some c => String.beq c.dir "." && String.beq c.host "127.0.0.1" && U16.beq c.port 8000u16,
        Option.none => false,
    }

#[test]
def test_static_positional_dir : Bool :=
    match decoded ["static", "docs/public"] {
        Option.some c => String.beq c.dir "docs/public" && U16.beq c.port 8000u16,
        Option.none => false,
    }

#[test]
def test_static_port_and_host : Bool :=
    match decoded ["static", "site", "--port", "9000", "--host", "0.0.0.0"] {
        Option.some c => String.beq c.dir "site" && String.beq c.host "0.0.0.0" && U16.beq c.port 9000u16,
        Option.none => false,
    }

#[test]
def test_bad_port_is_error : Bool :=
    match ok_parsed (Cli.parse StaticCli.spec ["static", "--port", "70000"]) {
        Option.none => false,
        Option.some p =>
            match StaticCli.decode p {
                Result.ok _ => false,
                Result.err e => String.contains e "--port",
            },
    }

#[test]
def test_help_lists_static : Bool :=
    match Cli.parse StaticCli.spec ["static", "--help"] {
        Cli.ParseResult.parse_help text => String.contains text "static" && String.contains text "DIR",
        _ => false,
    }
