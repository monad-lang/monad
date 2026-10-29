// The crypto mote's library root -- bare `use crypto` resolves here.
//
// Name paths, not bare names: `Ct.eq` is the declaration's own spelling.
// The pure codecs live in `std` (`std::base64`, `std::hex`) and the
// `Random` class in `std::random`; this mote supplies the OpenSSL
// implementation as `crypto::random`'s source type and its instance,
// which consumers reach by importing that module.

pub use lib::types {CryptoSigAlg, CryptoPublicKey}
pub use lib::ct {Ct.eq}
