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
use elf {Elf, ElfHeader, ProgramHeader, parse, class_known, endian_known}
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
    match r {
        Result.err _ => return false,
        Result.ok elf =>
            let h : ElfHeader := elf_header elf in
            return (I64.beq h.cls 2 && class_known h.cls
                && endian_known 1
                && I64.beq h.file_type 2
                && I64.beq h.machine 62
                && I64.beq h.entry 0x401000
                && I64.beq h.phoff 64
                && I64.beq h.phnum 1
                && I64.beq h.ehsize 64
                && I64.beq h.phentsize 56)
    }
}

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
    match r {
        Result.err _ => return false,
        Result.ok elf => return (first_ph_is_load elf)
    }
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
    match parse bytes {
        Result.err _ => return true,
        Result.ok _ => return false
    }
}

/// A non-ELF file is rejected at offset 0.
#[cfg {feature := "buf"}]
#[test]
def test_bad_magic_fails : IO Bool := do {
    let buf <- Buf.of_list [1u8, 2u8, 3u8, 4u8];
    let bytes : Bytes := Bytes.of_buf (Shared.of buf);
    match parse bytes {
        Result.err e => return (I64.beq (ParseError.error_offset e) 0),
        Result.ok _ => return false
    }
}
