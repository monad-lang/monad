/// `grep`/`glob` -- via `Proc.capture`, adequate for one-shot
/// read-only tools (agent-skills.md Phase 2's own framing; the real
/// piped-subprocess surface is Phase 4). `Proc.capture` shells out
/// through `sh -c` internally and already quotes each argument itself
/// (`Proc.quoted_argv`) -- callers pass a plain argv list, not a
/// pre-quoted string.
use init::transformers {ResultT}
use shuttle::message_types {Content}
use shuttle::tools::search_args {GrepArgs, GlobArgs}
use json::json {Json}
use std::process {Proc.capture}

def tool_err (id : String) (msg : String) : Content := Content.tool_result id msg true
def tool_ok (id : String) (msg : String) : Content := Content.tool_result id msg false

def capture_result (id : String) (cmd : String) (args : List String) : IO Content := do {
    let outcome <- Proc.capture cmd args;
    return (match outcome {
        Pair.pair code output =>
            if code == 0 then tool_ok id output
            else tool_err id output,
    })
}

pub def grep_run (id : String) (j : Json) : ResultT String IO Content :=
    match GrepArgs.deserialize_json j {
        Result.err e => ResultT.mk (return (Result.ok (tool_err id e))),
        Result.ok args =>
            ResultT.mk (do {
                let c <- capture_result id "grep" ["-rn", args.pattern, args.path];
                return (Result.ok c)
            }),
    }

pub def glob_run (id : String) (j : Json) : ResultT String IO Content :=
    match GlobArgs.deserialize_json j {
        Result.err e => ResultT.mk (return (Result.ok (tool_err id e))),
        Result.ok args =>
            ResultT.mk (do {
                let c <- capture_result id "find" [args.path, "-name", args.pattern];
                return (Result.ok c)
            }),
    }
