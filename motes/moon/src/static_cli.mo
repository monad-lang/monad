/// `moon static [DIR] [--port N] [--host H]`: the argument surface of the
/// static preview server, split from `main.mo` so parsing is testable
/// without binding a socket.
///
/// The defaults match `python3 -m http.server`: serve `.` on
/// `127.0.0.1:8000`.
use clap::spec {
    Cli.ArgValue, Cli.CommandSpec, Cli.Parsed, Cli.command, Cli.option_default,
    Cli.positional_optional, Cli.with_args, Cli.with_subcommands, Cli.with_version,
}

/// Where to serve from and what to bind.
pub struct StaticCli {
    dir : String,
    host : String,
    port : U16,
}

pub instance Copy StaticCli {
    def copy (c : StaticCli) : Pair StaticCli StaticCli := Pair.pair c c
}

pub def StaticCli.default : StaticCli :=
    { dir := ".", host := "127.0.0.1", port := 8000u16 }

pub def StaticCli.spec : Cli.CommandSpec :=
    Cli.with_subcommands
        [Cli.with_args
            [Cli.positional_optional "DIR" "the directory to serve (default: .)",
                Cli.option_default "port" "p" "PORT" "8000" "port to listen on (default: 8000)",
                Cli.option_default "host" "H" "HOST" "127.0.0.1" "address to bind (default: 127.0.0.1)"]
            (Cli.command "static" "Serve a directory over HTTP")]
        (Cli.with_version "0.1.0" (Cli.command "moon" "Monad web tooling"))

/// The digit `d` (0..9) as U16. There is no `U16.of_i64`; the list is the
/// same lookup `motes/oak_ui_book/scripts/serve.mo` uses.
#[terminating]
def digit_u16 (i : I64) (ds : List U16) : U16 :=
    match ds {
        List.empty => 0u16,
        List.cons d rest => if I64.beq i 0 then d else digit_u16 (I64.sub i 1) rest,
    }

/// A port in 1..65535. The I64 shadow catches overflow before the U16
/// wraps; copied from `motes/oak_ui_book/scripts/serve.mo`, which has
/// served the explorer's preview since it landed.
#[terminating]
def parse_port_go (bytes : List U8) (acc : U16) (wide : I64) : Option U16 :=
    match bytes {
        List.empty => if I64.lt 0 wide then Option.some acc else Option.none,
        List.cons b rest =>
            let d : I64 := U8.to_i64 b - 48 in
            if d < 0 || I64.gt d 9
            then Option.none
            else
                let next_wide : I64 := wide * 10 + d in
                if I64.gt next_wide 65535
                then Option.none
                else parse_port_go rest (U16.add (U16.mul acc 10u16) (digit_u16 d [0u16, 1u16, 2u16, 3u16, 4u16, 5u16, 6u16, 7u16, 8u16, 9u16])) next_wide,
    }

pub def StaticCli.parse_port (s : String) : Option U16 :=
    if String.is_empty s then Option.none else parse_port_go (String.to_list s) 0u16 0

/// Fold the parsed options onto the defaults (`option_default` documents the
/// value in help; the parser does not materialise it, so decoding supplies
/// it here, as `acorn`'s CLI does).
def apply_options (opts : List Cli.ArgValue) (acc : StaticCli) : Result String StaticCli :=
    match opts {
        List.empty => Result.ok acc,
        List.cons o rest =>
            match apply_option o acc {
                Result.err e => Result.err e,
                Result.ok next => apply_options rest next,
            },
    }

def apply_option (o : Cli.ArgValue) (acc : StaticCli) : Result String StaticCli :=
    match o {
        { name, value } =>
            if String.beq name "port"
            then
                match StaticCli.parse_port value {
                    Option.some port => Result.ok { acc with port := port },
                    Option.none => Result.err (String.concat "--port: not a port (1-65535): " value),
                }
            else if String.beq name "host" then Result.ok { acc with host := value }
            else Result.ok acc,
    }

/// The first positional, when present and non-empty (an empty DIR is `.`).
def positional_dir (positionals : List Cli.ArgValue) : Option String :=
    match positionals {
        List.empty => Option.none,
        List.cons a _ => if String.is_empty a.value then Option.none else Option.some a.value,
    }

def with_dir (dir : Option String) (c : StaticCli) : StaticCli :=
    match dir {
        Option.none => c,
        Option.some d => { c with dir := d },
    }

pub def StaticCli.decode (p : Cli.Parsed) : Result String StaticCli :=
    match p {
        { options, positionals, .. } =>
            let dir : Option String := positional_dir positionals in
            match apply_options options StaticCli.default {
                Result.err e => Result.err e,
                Result.ok opts => Result.ok (with_dir dir opts),
            },
    }
