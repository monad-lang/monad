/// `Provider.list_models`'s offline arm: the mock wire answers its one
/// scripted name, so the weaver's `/models` path is testable without a
/// socket or a key.
use shuttle::provider {Provider.list_models, ProviderConfig, Wire}

def mock_cfg : ProviderConfig :=
  { base_url := "mock", model := "mock", api_key_env := "WEAVER_UNUSED_KEY", max_tokens := 8, wire := Wire.mock }

#[test]
def test_mock_list_models_returns_mock : IO Bool := do {
  let r <- Provider.list_models mock_cfg;
  return (match r {
    Result.ok models => models == ["mock"],
    Result.err _ => false,
  })
}
