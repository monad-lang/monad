// The tls mote's library root -- bare `use tls` resolves here.
//
// Deliberately EMPTY, following motes/http/src/lib.mo: `ffi` (the raw
// `#[extern "c"]` OpenSSL declarations) and `stream` (`Tls.Stream`,
// `Tls.connect`/`read`/`write`/`close`) work from other motes because
// package-private still crosses mote boundaries today. A re-export list
// here would freeze the "which of these are the API?" question before
// anyone needs it answered; `use tls::stream {Tls.connect}` resolves
// directly today.