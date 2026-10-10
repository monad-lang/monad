use shuttle::message {Message, Usage, Turn}
use shuttle::message_types {Role, Content, StopReason}
use json::json {Json}

#[test]
def test_role_roundtrip : Bool :=
    match Role.deserialize_json (Role.serialize_json Role.assistant) {
        Result.ok r =>
            match r { Role.assistant => true, _ => false },
        Result.err _ => false,
    }

#[test]
def test_content_tool_use_roundtrip : Bool :=
    let c : Content := Content.tool_use "call_1" "grep" (Json.str "x") in
    match Content.deserialize_json (Content.serialize_json c) {
        Result.ok c2 =>
            match c2 {
                Content.tool_use id name input => String.beq id "call_1" && String.beq name "grep",
                _ => false,
            },
        Result.err _ => false,
    }

#[test]
def test_stop_reason_other_roundtrip : Bool :=
    match StopReason.deserialize_json (StopReason.serialize_json (StopReason.other "weird")) {
        Result.ok sr =>
            match sr {
                StopReason.other s => String.beq s "weird",
                _ => false,
            },
        Result.err _ => false,
    }

#[test]
def test_turn_roundtrip : Bool :=
    let msg : Message := { role := Role.assistant, content := [Content.text "hi"] } in
    let usage : Usage := { input_tokens := 1, output_tokens := 2, cached_tokens := 0 } in
    let turn : Turn := { message := msg, usage := usage, stop := StopReason.end_turn } in
    match Turn.deserialize_json (Turn.serialize_json turn) {
        Result.ok turn2 =>
            match turn2 {
                Turn.mk msg2 usage2 stop2 =>
                    match stop2 {
                        StopReason.end_turn =>
                            match msg2 { Message.mk role content => match role { Role.assistant => true, _ => false } },
                        _ => false,
                    }
            },
        Result.err _ => false,
    }
