/// `monadup new`: a minimal, buildable project.
use lib::shell {*}

/// A project name is written verbatim into `mote.toml` and the generated
/// `main.mo`, so it is restricted to `[A-Za-z0-9_.-]`. In particular a
/// quote or newline would otherwise produce invalid metadata (or inject
/// lines) while the command reported success.
def Scaffold.valid_byte (b : U8) : Bool :=
    (U8.gt b 47u8 && U8.gt 58u8 b)
        || (U8.gt b 64u8 && U8.gt 91u8 b)
        || (U8.gt b 96u8 && U8.gt 123u8 b)
        || U8.beq b 95u8
        || U8.beq b 45u8
        || U8.beq b 46u8

#[partial]
def Scaffold.valid_bytes (bs : List U8) : Bool :=
    match bs {
        List.empty => true,
        List.cons b rest => if Scaffold.valid_byte b then Scaffold.valid_bytes rest else false,
    }

pub def Scaffold.validate_name (name : String) : Result String String :=
    if String.is_empty name then Result.err "project name must not be empty"
    else if String.beq name "." || String.beq name ".." then Result.err "project name must not be '.' or '..'"
    else if String.beq (String.slice name 0 1) "-" then Result.err "project name must not start with '-'"
    else if Scaffold.valid_bytes (String.to_list name) then Result.ok name
    else Result.err "project name may contain only letters, digits, '_', '-' and '.'"

pub def Scaffold.manifest (name : String) : String :=
    String.concat "[mote]\nname = \"" (String.concat name
        (String.concat "\"\nversion = \"0.1.0\"\nedition = \"2026\"\n\n[[bin]]\nname = \""
            (String.concat name "\"\npath = \"src/main.mo\"\n")))

pub def Scaffold.main_source (name : String) : String :=
    String.concat "open IO {println}\n\ndef main (args : List String) : IO Unit := println \"Hello from " (String.concat name "!\"\n")

pub def Scaffold.readme (name : String) : String :=
    String.concat "# " (String.concat name "\n\nA Monad project.\n\n```bash\nmonad run .\n```\n")

pub def Scaffold.gitignore : String := "target/\n*.ll\n"

pub def Scaffold.target_dir (base : Option String) (name : String) : String :=
    match base {
        Option.some b => String.concat b (String.concat "/" name),
        Option.none => name,
    }

/// `IO.write_file`'s native returns silently when `fopen` fails, so a
/// write is confirmed by reading the file back. A short or missing file
/// therefore fails the command instead of printing "created".
#[partial]
def Scaffold.write_checked (path : String) (content : String) : IO (Result String Unit) := do {
    Shell.write_file path content;
    let exists <- Shell.file_exists path;
    if Bool.not exists then return (Result.err (String.concat "failed to write " path))
    else do {
        let back <- Shell.read_file path;
        if String.beq back content
        then return (Result.ok unit)
        else return (Result.err (String.concat "failed to write " path))
    }
}

#[partial]
def Scaffold.write_all (files : List (Pair String String)) : IO (Result String Unit) :=
    match files {
        List.empty => return (Result.ok unit),
        List.cons p rest =>
            match p {
                Pair.pair path content => do {
                    let r <- Scaffold.write_checked path content;
                    match r {
                        Result.err e => return (Result.err e),
                        Result.ok _ => Scaffold.write_all rest,
                    }
                },
            },
    }

pub def Scaffold.create (base : Option String) (name : String) : IO (Result String String) := do {
    match Scaffold.validate_name name {
        Result.err e => return (Result.err e),
        Result.ok n => do {
            let dir : String := Scaffold.target_dir base n;
            let exists <- Shell.file_exists dir;
            let isdir <- Shell.is_dir dir;
            if exists || isdir then return (Result.err (String.concat "destination already exists: " dir))
            else do {
                let mk <- Shell.mkdir_p (String.concat dir "/src");
                if Bool.not (I64.beq mk 0) then return (Result.err (String.concat "failed to create " dir))
                else do {
                    let files : List (Pair String String) := [
                        (String.concat dir "/mote.toml", Scaffold.manifest n),
                        (String.concat dir "/src/main.mo", Scaffold.main_source n),
                        (String.concat dir "/README.md", Scaffold.readme n),
                        (String.concat dir "/.gitignore", Scaffold.gitignore),
                    ];
                    let written <- Scaffold.write_all files;
                    match written {
                        Result.err e => do {
                            let _ <- Shell.rm_rf dir;
                            return (Result.err e)
                        },
                        Result.ok _ => return (Result.ok dir),
                    }
                }
            }
        },
    }
}
