// Read a TOML file passed on the command line, parse it, and print the result.
//
// Usage: monad run examples/toml.mo <file.toml>

// TODO: `BTreeMap` is used as a bare type annotation below but is
// deliberately NOT listed here — see the matching TODO in
// std/map_tests.mo for why (a pre-existing latent instance/dictionary-
// resolution bug this explicit filter exposes).
use std.map {}
use lang.toml {ParseError, Value, parse, to_string}

def print_parse_error (e : Toml.ParseError) : IO Unit :=
  IO.println (String.concat "Parse error: " (Toml.ParseError.to_string e))

def print_parsed (r : Result Toml.ParseError (BTreeMap String Toml.Value)) : IO Unit :=
  match r {
    ok t => IO.println (Toml.to_string t),
    err e => print_parse_error e
  }

def run_file (path : String) : IO Unit {
  match Path.of path {
    err e => IO.println (String.concat "invalid path: " e),
    ok p => do {
      let exists <- IO.file_exists p;
      if exists
      then do {
        let content <- IO.read_file p;
        print_parsed (Toml.parse content)
      }
      else IO.println (String.concat "File not found: " path)
    },
  }
}

def main (args : List String) : IO Unit :=
  match List.last args {
    Option.some path => run_file path,
    Option.none => IO.println "usage: monad run examples/toml.mo <file.toml>"
  }
