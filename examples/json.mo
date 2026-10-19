// Read a JSON file passed on the command line, parse it, and print the result.
//
// Usage: monad run examples/json.mo <file.json>
#![mote { name := "json", deps := [lang] }]


use json::json {Json}
use std::stream {StreamError}

def print_parse_error (e : Json.ParseError) : IO Unit :=
  IO.println (String.concat "Parse error: " (Json.ParseError.to_string e))

def print_parsed (r : Result Json.ParseError Json) : IO Unit :=
  match r {
    ok j => IO.println (Json.to_string j),
    err e => print_parse_error e
  }

def run_file (path : String) : IO Unit {
  match Path.of path {
    err e => IO.println (String.concat "invalid path: " e),
    ok p => do {
      let r <- IO.read_file p;
      print_read path r
    },
  }
}

def print_read (path : String) (r : Result StreamError String) : IO Unit :=
  match r {
    Result.err e => IO.println ("cannot read " ++ path ++ ": " ++ e.message),
    Result.ok content => print_parsed (Json.parse content)
  }

def main (args : List String) : IO Unit :=
  match List.last args {
    Option.some path => run_file path,
    Option.none => IO.println "usage: monad run examples/json.mo <file.json>"
  }
