// IO is ambient (init/io.mo, always a loaded root) -- no `use` needed.

#[native "exec_cmd"]
def exec_cmd (cmd : String) (args : List String) : IO I64
