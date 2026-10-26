/// Unit tests for the REPL session core: classification, persistent
/// declarations and `use`, expression value/type rendering, `:type`,
/// `:reset`, and multi-line continuation. No stdin is involved -- `classify`
/// and `step` are the whole machine the CLI loops over.

use lib::session {
    EvalSession, EvalResponse, EvalInput,
    Eval.new_session, Eval.classify, Eval.step,
}

def session_path : String := "repl.mo"

def run_line (s : EvalSession) (text : String) : IO (Pair EvalSession EvalResponse) := do {
    let classified := Eval.classify s text;
    match classified {
        Pair.pair s2 input => Eval.step s2 input,
    }
}

/// The response only, when a test does not need the advanced session.
def respond (s : EvalSession) (text : String) : IO EvalResponse := do {
    let p <- run_line s text;
    match p {
        Pair.pair _ r => IO.pure r,
    }
}

/// The advanced session only, when a test does not need the response.
def advance (s : EvalSession) (text : String) : IO EvalSession := do {
    let p <- run_line s text;
    match p {
        Pair.pair s2 _ => IO.pure s2,
    }
}

def value_of (r : EvalResponse) : Option String :=
    match r {
        EvalResponse.eval_response_value text _ _ => Option.some text,
        _ => Option.none,
    }

def type_of (r : EvalResponse) : Option String :=
    match r {
        EvalResponse.eval_response_value _ typ _ => Option.some typ,
        _ => Option.none,
    }

def meta_of (r : EvalResponse) : Option String :=
    match r {
        EvalResponse.eval_response_meta text => Option.some text,
        _ => Option.none,
    }

def is_ok (r : EvalResponse) : Bool :=
    match r {
        EvalResponse.eval_response_ok _ => true,
        _ => false,
    }

def is_error (r : EvalResponse) : Bool :=
    match r {
        EvalResponse.eval_response_error _ => true,
        _ => false,
    }

def is_continue (input : EvalInput) : Bool :=
    match input {
        EvalInput.eval_input_continue => true,
        _ => false,
    }

#[test]
def test_expression_value_and_type : IO Bool := do {
    let s <- Eval.new_session session_path;
    let r <- respond s "2 + 3";
    match value_of r {
        Option.some text =>
            IO.pure (String.beq text "5"
                && match type_of r {
                    Option.some typ => String.beq typ "I64",
                    Option.none => false,
                }),
        Option.none => IO.pure false,
    }
}

#[test]
def test_definitions_persist : IO Bool := do {
    let s <- Eval.new_session session_path;
    let r1 <- respond s "def twice (n : I64) : I64 := n + n";
    let s1 <- advance s "def twice (n : I64) : I64 := n + n";
    let r2 <- respond s1 "twice 21";
    match value_of r2 {
        Option.some text => IO.pure (is_ok r1 && String.beq text "42"),
        Option.none => IO.pure false,
    }
}

/// A declaration whose body does not typecheck is rejected, and every
/// earlier definition stays usable.
#[test]
def test_rejected_definition_keeps_the_session : IO Bool := do {
    let s <- Eval.new_session session_path;
    let r1 <- respond s "def good : I64 := 11";
    let s1 <- advance s "def good : I64 := 11";
    let r2 <- respond s1 "def bad : I64 := nope";
    let s2 <- advance s1 "def bad : I64 := nope";
    let r3 <- respond s2 "good";
    match value_of r3 {
        Option.some text => IO.pure (is_ok r1 && is_error r2 && String.beq text "11"),
        Option.none => IO.pure false,
    }
}

/// `use` is an ordinary declaration: it joins the session and the next
/// step resolves it through the standard filesystem loader.
#[test]
def test_use_is_supported : IO Bool := do {
    let s <- Eval.new_session session_path;
    let r1 <- respond s "use init::foldable {}";
    let s1 <- advance s "use init::foldable {}";
    let r2 <- respond s1 "1 + 2";
    match value_of r2 {
        Option.some text => IO.pure (is_ok r1 && String.beq text "3"),
        Option.none => IO.pure false,
    }
}

/// A `def` body on the next line is a continuation, not a parse error: the
/// first line fails at end of input, the combined text parses.
#[test]
def test_multiline_definition_continues : IO Bool := do {
    let s <- Eval.new_session session_path;
    let first : EvalInput :=
        match Eval.classify s "def inc (n : I64) : I64 :=" {
            Pair.pair _ input => input,
        };
    if is_continue first then multiline_body s else IO.pure false
}

def multiline_body (s : EvalSession) : IO Bool := do {
    let combined : String := "def inc (n : I64) : I64 :=\n    n + 1";
    let r1 <- respond s combined;
    let s1 <- advance s combined;
    let r2 <- respond s1 "inc 41";
    match value_of r2 {
        Option.some text => IO.pure (is_ok r1 && String.beq text "42"),
        Option.none => IO.pure false,
    }
}

#[test]
def test_type_command_does_not_evaluate : IO Bool := do {
    let s <- Eval.new_session session_path;
    let r <- respond s ":type 2 + 3";
    match meta_of r {
        Option.some text => IO.pure (String.contains text "I64"),
        Option.none => IO.pure false,
    }
}

#[test]
def test_reset_forgets_definitions : IO Bool := do {
    let s <- Eval.new_session session_path;
    let s1 <- advance s "def seven : I64 := 7";
    let r2 <- respond s1 ":reset";
    let s2 <- advance s1 ":reset";
    let r3 <- respond s2 "seven";
    match meta_of r2 {
        Option.some _ => IO.pure (is_error r3),
        Option.none => IO.pure false,
    }
}

#[test]
def test_unknown_meta_is_an_error : IO Bool := do {
    let s <- Eval.new_session session_path;
    let r <- respond s ":nope";
    IO.pure (is_error r)
}
