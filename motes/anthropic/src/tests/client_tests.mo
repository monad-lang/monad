/// The Anthropic model-list decoder: the same `data[].id` shape as the
/// OpenAI-compatible hosts, so the pure parse half is what these pin.
use anthropic::client {Anthropic.parse_models}

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
