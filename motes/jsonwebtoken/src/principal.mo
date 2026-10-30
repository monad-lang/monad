/// The authenticated identity a validated token yields.
///
/// OAuth's own `Principal` projection lands here rather than in `oauth`,
/// because any JWT consumer needs the same fields. `claims` is the full
/// claim map, so an application can read a provider-specific claim without
/// this mote growing a field for it.

use std::map {BTreeMap}
use json::json {Json}

pub struct Principal {
  subject : String,
  issuer : String,
  audiences : List String,
  scopes : List String,
  roles : List String,
  claims : BTreeMap String Json,
  /// Epoch seconds, from `exp`.
  expires_at : I64
}
