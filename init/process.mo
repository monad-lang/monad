use io {IO}

#[native "exec_cmd"]
def exec_cmd (cmd : String) (args : List String) : IO I64
