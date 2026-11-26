// The ELF library root: bare `use elf` resolves here.
//
// One module's `pub` surface. A consumer that calls `Elf.parse` also needs
// `parsec::input.Bytes` (and, for the error, `parsec::core.ParseError`); it
// imports those FROM `parsec`, not through this hub -- a mote's lib root does
// not re-export another mote's declarations (measured: `use elf {Bytes}`
// reports "`elf` declares no `Bytes`").
pub use lib::elf {
    Elf, ElfHeader, ProgramHeader, SectionHeader, Symbol,
    class_known, endian_known, header, parse,
}
