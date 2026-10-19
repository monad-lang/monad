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
    "[mote]\nname = \"" ++ name
        ++ "\"\nversion = \"0.1.0\"\nedition = \"2026\"\n\n[[bin]]\nname = \""
        ++ name ++ "\"\npath = \"src/main.mo\"\n"

pub def Scaffold.main_source (name : String) : String :=
    "open IO {println}\n\ndef main (args : List String) : IO Unit := println \"Hello from " ++ name ++ "!\"\n"

pub def Scaffold.readme (name : String) : String :=
    "# " ++ name ++ "\n\nA Monad project.\n\n```bash\nmonad run .\n```\n"

pub def Scaffold.gitignore : String := "target/\n*.ll\n"

/// `name` must already satisfy `validate_name`: it is a single path
/// component, so it cannot replace `base` in the join.
pub def Scaffold.target_dir (base : Option String) (name : String) : Result String Path :=
    match base {
        Option.some b =>
            match Path.of b {
                Result.ok dir => Result.ok (Path.join dir (Path.path name)),
                Result.err e => Result.err e,
            },
        Option.none => Path.of name,
    }

/// `IO.write_file`'s native returns silently when `fopen` fails, so a
/// write is confirmed by reading the file back. A short or missing file
/// therefore fails the command instead of printing "created".
#[partial]
def Scaffold.write_checked (path : Path) (content : String) : IO (Result String Unit) := do {
    let w <- Shell.write_file path content;
    match w {
        Result.err e => return (Result.err e),
        Result.ok _ => do {
            let exists <- Shell.file_exists path;
            if Bool.not exists then return (Result.err ("failed to write " ++ Path.to_string path))
            else do {
                let back <- Shell.read_file path;
                match back {
                    Result.err e => return (Result.err e),
                    Result.ok text =>
                        if String.beq text content
                        then return (Result.ok unit)
                        else return (Result.err ("failed to write " ++ Path.to_string path)),
                }
            }
        },
    }
}

#[partial]
def Scaffold.write_all (files : List (Pair Path String)) : IO (Result String Unit) :=
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

pub def Scaffold.create (base : Option String) (name : String) : IO (Result String Path) := do {
    match Scaffold.validate_name name {
        Result.err e => return (Result.err e),
        Result.ok n => do {
            match Scaffold.target_dir base n {
                Result.err e => return (Result.err e),
                Result.ok dir => do {
                    let exists <- Shell.file_exists dir;
                    let isdir <- Shell.is_dir dir;
                    if exists || isdir then return (Result.err ("destination already exists: " ++ Path.to_string dir))
                    else do {
                        let src_dir : Path := Path.join dir (Path.path "src");
                        let mk <- Shell.mkdir_p src_dir;
                        if Bool.not (I64.beq mk 0) then return (Result.err ("failed to create " ++ Path.to_string dir))
                        else do {
                            let files : List (Pair Path String) := [
                                (Path.join dir (Path.path "mote.toml"), Scaffold.manifest n),
                                (Path.join src_dir (Path.path "main.mo"), Scaffold.main_source n),
                                (Path.join dir (Path.path "README.md"), Scaffold.readme n),
                                (Path.join dir (Path.path ".gitignore"), Scaffold.gitignore),
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
        },
    }
}
