// The jsonwebtoken mote's library root -- bare `use jsonwebtoken`
// resolves here.
//
// Name paths, not bare names: the declaration's own spelling is what a
// brace item matches. `Jwt.parse` and `Claims.validate_*` are public for
// tests and auditing, but they do NOT establish trust; the safe entry
// points are `Claims.check_id_token` and `Claims.check_access_token`,
// which verify the signature before reading a claim.

pub use lib::errors {JwtError, JwtError.to_string}
pub use lib::alg {Alg.name, Alg.parse}
pub use lib::principal {Principal}
pub use lib::jwt {Jwt, Jwt.parse, Jwt.verify}
pub use lib::jwks {Jwks.key_for}
pub use lib::claims {
  Claims.check_access_token,
  Claims.check_id_token,
  Claims.validate_access_token,
  Claims.validate_id_token,
  ClaimsConfig,
}
pub use lib::verifier {
  JwtVerifier,
  JwtVerifier.fake,
  JwtVerifier.real,
  JwtVerifier.run,
}
