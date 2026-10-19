/// `monadup new`: a minimal, buildable project.
use lib::text {*}
use lib::shell {*}

#[partial]
def Scaffold.has_forbidden_char (name : String) (i : I64) : Bool :=
    if I64.lt i (String.length name) then
        let c : String := String.slice name i 1 in
        if String.beq c "/" || String.beq c "\\" || String.beq c " " || String.beq c ":" || String.beq c "\t"
        then true
        else Scaffold.has_forbidden_char name (I64.add i 1)
    else false

pub def Scaffold.validate_name (name : String) : Result String String :=
    if String.is_empty name then Result.err "project name must not be empty"
    else if String.beq name "." || String.beq name ".." then Result.err "project name must not be '.' or '..'"
    else if String.beq (String.slice name 0 1) "-" then Result.err "project name must not start with '-'"
    else if Scaffold.has_forbidden_char name 0 then Result.err "project name must not contain '/', '\\', spaces, ':' or tabs"
    else Result.ok name

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

pub def Scaffold.create (base : Option String) (name : String) : IO (Result String String) := do {
    match Scaffold.validate_name name {
        Result.err e => return (Result.err e),
        Result.ok n => do {
            let dir : String := Scaffold.target_dir base n;
            let exists <- Shell.file_exists dir;
            let isdir <- Shell.is_dir dir;
            if exists || isdir then return (Result.err (String.concat "destination already exists: " dir))
            else do {
                let _ <- Shell.mkdir_p (String.concat dir "/src");
                Shell.write_file (String.concat dir "/mote.toml") (Scaffold.manifest n);
                Shell.write_file (String.concat dir "/src/main.mo") (Scaffold.main_source n);
                Shell.write_file (String.concat dir "/README.md") (Scaffold.readme n);
                Shell.write_file (String.concat dir "/.gitignore") Scaffold.gitignore;
                return (Result.ok dir)
            }
        },
    }
}
