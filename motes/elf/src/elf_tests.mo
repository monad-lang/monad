/// Tests for the ELF parser, over handcrafted images -- the smallest
/// `Elf64` little-endian executable that exercises the header, one program
/// header and the section-table walk.
///
/// Gated on the `buf` feature with the rest of the binary-input path: the
/// fixture has to become a `Buf U8`, and `Buf.of_list` is a native the
/// current nightly does not carry yet (`bootstrap/next-features.txt`).
use std::buf {Buf}
use std::buf {}
use parsec::core {ParseError, ParseResult}
use parsec::input {Input, Bytes}
use elf {
    Elf, ElfHeader, ProgramHeader, SectionHeader, class_known, endian_known, parse,
}
open ParseResult {fail, success}

/// A 64-byte `Elf64` header + one 56-byte `PT_LOAD` program header.
/// Little-endian throughout, which is what `EI_DATA = 1` declares.
#[cfg {feature := "buf"}]
def fixture : List U8 := [
    // e_ident: magic, ELF64, little, version 1, osabi 0, abiversion 0, pad
    0x7Fu8, 0x45u8, 0x4Cu8, 0x46u8, 2u8, 1u8, 1u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8,
    // e_type = ET_EXEC (2), e_machine = EM_X86_64 (62), e_version = 1
    2u8, 0u8, 62u8, 0u8, 1u8, 0u8, 0u8, 0u8,
    // e_entry = 0x401000
    0x00u8, 0x10u8, 0x40u8, 0u8, 0u8, 0u8, 0u8, 0u8,
    // e_phoff = 64
    64u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8,
    // e_shoff = 0
    0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8,
    // e_flags = 0
    0u8, 0u8, 0u8, 0u8,
    // e_ehsize = 64, e_phentsize = 56, e_phnum = 1
    64u8, 0u8, 56u8, 0u8, 1u8, 0u8,
    // e_shentsize = 64, e_shnum = 0, e_shstrndx = 0
    64u8, 0u8, 0u8, 0u8, 0u8, 0u8,
    // program header: p_type = PT_LOAD (1), p_flags = R|X (5)
    1u8, 0u8, 0u8, 0u8, 5u8, 0u8, 0u8, 0u8,
    // p_offset = 0
    0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8,
    // p_vaddr = 0x400000
    0x00u8, 0x00u8, 0x40u8, 0u8, 0u8, 0u8, 0u8, 0u8,
    // p_paddr = 0x400000
    0x00u8, 0x00u8, 0x40u8, 0u8, 0u8, 0u8, 0u8, 0u8,
    // p_filesz = 0x100
    0x00u8, 0x01u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8,
    // p_memsz = 0x100
    0x00u8, 0x01u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8,
    // p_align = 0x1000
    0x00u8, 0x10u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8,
]

#[cfg {feature := "buf"}]
def parsed : IO (Result ParseError Elf) := do {
    let buf <- Buf.of_list fixture;
    let bytes : Bytes := Bytes.of_buf (Shared.of buf);
    return (parse bytes)
}

#[cfg {feature := "buf"}]
#[test]
def test_header_fields : IO Bool := do {
    let r <- parsed;
    return (match r {
        Result.err _ => false,
        Result.ok elf => header_fields_ok elf
    })
}

#[cfg {feature := "buf"}]
def header_fields_ok (elf : Elf) : Bool :=
    let h : ElfHeader := elf_header elf in
    I64.beq h.cls 2 && class_known h.cls
        && endian_known 1
        && I64.beq h.file_type 2
        && I64.beq h.machine 62
        && I64.beq h.entry 0x401000
        && I64.beq h.phoff 64
        && I64.beq h.phnum 1
        && I64.beq h.ehsize 64
        && I64.beq h.phentsize 56

/// `Elf` is affine, so its header comes out through a field pattern (one
/// use of the record, one binder) rather than a projection.
#[cfg {feature := "buf"}]
def elf_header (elf : Elf) : ElfHeader :=
    match elf {
        { header, .. } => header
    }

#[cfg {feature := "buf"}]
#[test]
def test_program_header_fields : IO Bool := do {
    let r <- parsed;
    return (match r {
        Result.err _ => false,
        Result.ok elf => first_ph_is_load elf
    })
}

#[cfg {feature := "buf"}]
def first_ph_is_load (elf : Elf) : Bool :=
    match elf {
        { program_headers, .. } => ph_matches program_headers
    }

#[cfg {feature := "buf"}]
def ph_matches (phs : List ProgramHeader) : Bool :=
    match phs {
        List.empty => false,
        List.cons p _ =>
            I64.beq p.p_type 1 && I64.beq p.flags 5
                && I64.beq p.vaddr 0x400000 && I64.beq p.filesz 0x100
                && I64.beq p.align 0x1000,
    }

/// A file with the magic but nothing else must FAIL the header (not crash,
/// not report an empty ELF).
#[cfg {feature := "buf"}]
#[test]
def test_truncated_file_fails : IO Bool := do {
    let buf <- Buf.of_list [0x7Fu8, 0x45u8, 0x4Cu8, 0x46u8];
    let bytes : Bytes := Bytes.of_buf (Shared.of buf);
    return (match parse bytes {
        Result.err _ => true,
        Result.ok _ => false
    })
}

/// A non-ELF file is rejected at offset 0.
#[cfg {feature := "buf"}]
#[test]
def test_bad_magic_fails : IO Bool := do {
    let buf <- Buf.of_list [1u8, 2u8, 3u8, 4u8];
    let bytes : Bytes := Bytes.of_buf (Shared.of buf);
    return (match parse bytes {
        Result.err e => I64.beq (ParseError.error_offset e) 0,
        Result.ok _ => false
    })
}

/// A 3-entry section table over the tiny string table `\0.shstrtab\0.text\0`.
/// The names live in a BOUNDED span (`Bytes.at`, cursor not at offset 0), which
/// is the case a whole-file scan cannot exercise: `Input.input_scan` must
/// answer a COUNT there, not the span's start offset.
#[cfg {feature := "buf"}]
def named_fixture : List U8 := [
    0x7Fu8, 0x45u8, 0x4Cu8, 0x46u8, 0x02u8, 0x01u8, 0x01u8, 0x00u8,
    0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8,
    0x01u8, 0x00u8, 0x3Eu8, 0x00u8, 0x01u8, 0x00u8, 0x00u8, 0x00u8,
    0x00u8, 0x10u8, 0x40u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8,
    0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8,
    0x40u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8,
    0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x40u8, 0x00u8, 0x00u8, 0x00u8,
    0x00u8, 0x00u8, 0x40u8, 0x00u8, 0x03u8, 0x00u8, 0x01u8, 0x00u8,
    0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8,
    0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8,
    0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8,
    0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8,
    0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8,
    0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8,
    0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8,
    0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8,
    0x01u8, 0x00u8, 0x00u8, 0x00u8, 0x03u8, 0x00u8, 0x00u8, 0x00u8,
    0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8,
    0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8,
    0x00u8, 0x01u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8,
    0x11u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8,
    0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8,
    0x01u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8,
    0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8,
    0x0Bu8, 0x00u8, 0x00u8, 0x00u8, 0x01u8, 0x00u8, 0x00u8, 0x00u8,
    0x06u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8,
    0x00u8, 0x10u8, 0x40u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8,
    0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8,
    0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8,
    0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8,
    0x10u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8,
    0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8,
    0x00u8, 0x2Eu8, 0x73u8, 0x68u8, 0x73u8, 0x74u8, 0x72u8, 0x74u8,
    0x61u8, 0x62u8, 0x00u8, 0x2Eu8, 0x74u8, 0x65u8, 0x78u8, 0x74u8,
    0x00u8,
]

#[cfg {feature := "buf"}]
def parse_named : IO (Result ParseError Elf) := do {
    let buf <- Buf.of_list named_fixture;
    let bytes : Bytes := Bytes.of_buf (Shared.of buf);
    return (parse bytes)
}

#[cfg {feature := "buf"}]
def section_named (sections : List SectionHeader) (i : I64) : String :=
    match sections {
        List.empty => "<missing>",
        List.cons s rest => if I64.beq s.index i then s.name else section_named rest i
    }

#[cfg {feature := "buf"}]
def sections_of (elf : Elf) : List SectionHeader :=
    match elf {
        { sections, .. } => sections
    }

#[cfg {feature := "buf"}]
def parsed_section_name (i : I64) : IO (Result ParseError String) := do {
    let r <- parse_named;
    return (match r {
        Result.err e => Result.err e,
        Result.ok elf => Result.ok (match elf {
            { sections, .. } => section_named sections i
        })
    })
}

#[cfg {feature := "buf"}]
#[test]
def test_shstrtab_section_name : IO Bool := do {
    let r <- parsed_section_name 1;
    return (match r {
        Result.err _ => false,
        Result.ok name => String.beq name ".shstrtab"
    })
}

#[cfg {feature := "buf"}]
#[test]
def test_text_section_name : IO Bool := do {
    let r <- parsed_section_name 2;
    return (match r {
        Result.err _ => false,
        Result.ok name => String.beq name ".text"
    })
}

/// `Input.input_scan` answers a COUNT from any cursor, not the absolute
/// buffer index it starts at: every caller (`bytes_while`, `name_at`) uses it
/// as a length. A bounded span is where the two answers differ.
#[cfg {feature := "buf"}]
#[test]
def test_scan_counts_within_a_bounded_span : IO Bool := do {
    let buf <- Buf.of_list [1u8, 1u8, 1u8, 0u8, 1u8, 1u8];
    let base : Bytes := Bytes.of_buf (Shared.of buf);
    let span : Bytes := Bytes.at base 1 4;
    let n : I64 := Input.input_scan (fn (x : U8) => U8.beq x 1u8) span;
    return (I64.beq n 2)
}
