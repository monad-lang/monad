// Read a JSON file passed on the command line, parse it, and print the result.
//
// Usage: monad run examples/json.mo <file.json>

use lang.json {Json, ParseError, parse, to_string}

def print_parse_error (e : Json.ParseError) : IO Unit :=
  IO.println (String.concat "Parse error: " (Json.ParseError.to_string e))

def print_parsed (r : Result Json.ParseError Json) : IO Unit :=
  match r {
    ok j => IO.println (Json.to_string j),
    err e => print_parse_error e
  }

def run_file (path : String) : IO Unit {
  let exists <- IO.file_exists path;
  if exists
  then do {
    let content <- IO.read_file path;
    print_parsed (Json.parse content)
  }
  else IO.println (String.concat "File not found: " path)
}

def main (args : List String) : IO Unit :=
  match List.last args {
    Option.some path => run_file path,
    Option.none => IO.println "usage: monad run examples/json.mo <file.json>"
  }
