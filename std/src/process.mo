// IO is ambient (init/io.mo, always a loaded root) -- no `use` needed.

#[native "exec_cmd"]
pub def exec_cmd (cmd : String) (args : List String) : IO I64

#[native "process_id"]
pub def process_id : I64
