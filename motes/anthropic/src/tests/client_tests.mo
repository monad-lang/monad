/// The Anthropic model-list decoder: the same `data[].id` shape as the
/// OpenAI-compatible hosts, so the pure parse half is what these pin.
use anthropic::client {Anthropic.parse_models, Anthropic.parse_messages}

#[test]
def test_parse_models_reads_ids : Bool :=
    match Anthropic.parse_models "{\"data\":[{\"type\":\"model\",\"id\":\"claude-a\"},{\"id\":\"claude-b\"}],\"has_more\":false}" {
        Result.ok ids => ids == ["claude-a", "claude-b"],
        Result.err _ => false,
    }

#[test]
def test_parse_models_accepts_an_empty_list : Bool :=
    match Anthropic.parse_models "{\"data\":[]}" {
        Result.ok ids => ids == [],
        Result.err _ => false,
    }

#[test]
def test_parse_models_rejects_missing_data : Bool :=
    match Anthropic.parse_models "{\"has_more\":false}" {
        Result.err e => String.contains e "missing data",
        Result.ok _ => false,
    }

/// F7: a truncated response body names its size and its tail -- "expected:
/// }" alone cannot tell a 40-byte reply from a 400 KB one.
#[test]
def test_a_truncated_messages_body_names_its_size_and_tail : Bool :=
    match Anthropic.parse_messages "{\"id\":\"m1\",\"content\":[" {
        Result.ok _ => false,
        Result.err e =>
            let msg : String := e in
            String.contains msg "bytes; tail:" && String.contains msg "\"content\":[",
    }
