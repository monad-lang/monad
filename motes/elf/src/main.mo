/// `elfinfo`: print what `elf` parsed about a binary -- the ELF header, the
/// program-header table, the section-header table and the symbol tables, in
/// the shape `readelf -h -l -S -s` uses.
///
/// The binary is the thin I/O shell: read the file into a `Buf U8`
/// (`IO.read_file_buf`), wrap it as a `parsec::input.Bytes` cursor, hand it to
/// `Elf.parse`, render what came back. All the parsing lives in `elf.mo`.
///
/// Gated on the `buf` feature with the rest of the binary-input path: it
/// calls `IO.read_file_buf`, a native that is wired in the tree but not yet
/// in a published nightly (`bootstrap/next-features.txt`).
use std::io {IO.write_stderr}
use std::io {}
use std::path {Path}
use clap::parse {Cli.run}
use clap::spec {
    Cli.CommandSpec, Cli.Parsed, Cli.command, Cli.flag, Cli.flag_set,
    Cli.positional, Cli.positional_values, Cli.with_args, Cli.with_name, Cli.with_version,
}
use elf {Elf, ElfHeader, ProgramHeader, SectionHeader, Symbol, parse}
use parsec::core {ParseError}
use parsec::input {Bytes}
use parsec::binary {Endian}

def spec : Cli.CommandSpec :=
    Cli.with_version "0.1.0"
        (Cli.with_name "elfinfo"
            (Cli.with_args
                [
                    Cli.positional "file" "the ELF file to describe",
                    Cli.flag "all" "a" "print the header, sections and symbols",
                    Cli.flag "headers" "h" "print the ELF header",
                    Cli.flag "program-headers" "l" "print the program-header table",
                    Cli.flag "sections" "S" "print the section-header table",
                    Cli.flag "symbols" "s" "print the symbol tables",
                ]
                (Cli.command "elfinfo" "Print information about an ELF binary")))

pub struct Args {
    file : String,
    all : Bool,
    headers : Bool,
    program_headers : Bool,
    sections : Bool,
    symbols : Bool,
}

instance Copy Args {
    def copy (a : Args) : Pair Args Args :=
        match a {
            mk file all headers program_headers sections symbols =>
                let x : Args := {
                    file := file, all := all, headers := headers,
                    program_headers := program_headers, sections := sections,
                    symbols := symbols } in
                let y : Args := {
                    file := file, all := all, headers := headers,
                    program_headers := program_headers, sections := sections,
                    symbols := symbols } in
                Pair.pair x y,
        }
}

def decode (p : Cli.Parsed) : Result String Args :=
    let args : Args := {
        file := first_or_empty (Cli.positional_values 0 p),
        all := Cli.flag_set "all" p,
        headers := Cli.flag_set "headers" p,
        program_headers := Cli.flag_set "program-headers" p,
        sections := Cli.flag_set "sections" p,
        symbols := Cli.flag_set "symbols" p,
    } in
    Result.ok args

def first_or_empty (xs : List String) : String :=
    match xs {
        List.empty => "",
        List.cons x _ => x
    }

// ─── Which sections to print ─────────────────────────────────────────
//
// No flags at all is the useful default (header + section list); `--all` is
// everything.

def show_headers (a : Args) : Bool :=
    a.all ||
        a.headers || (Bool.not a.headers && Bool.not a.sections && Bool.not a.symbols && Bool.not a.program_headers)

def show_sections (a : Args) : Bool :=
    a.all ||
        a.sections || (Bool.not a.headers && Bool.not a.sections && Bool.not a.symbols && Bool.not a.program_headers)

def show_program_headers (a : Args) : Bool :=
    a.all || a.program_headers

def show_symbols (a : Args) : Bool :=
    a.all || a.symbols

// ─── Rendering ───────────────────────────────────────────────────────

/// Lowercase hexadecimal, zero-padded to `width` digits -- there is no
/// `I64`->hex in `init/`, and growing the compiler-source surface for a
/// display detail of one binary is not worth it.
def hex (n : I64) (width : I64) : String :=
    hex_go n width ""

#[partial]
def hex_go (n : I64) (left : I64) (acc : String) : String :=
    if not (I64.lt 0 left)
    then acc
    else
        let digit : I64 := I64.sub n (I64.mul (I64.div n 16) 16) in
        let rest : I64 := I64.div n 16 in
        hex_go rest (left - 1) (String.concat (hex_digit digit) acc)

def hex_digit (d : I64) : String :=
    if I64.beq d 0 then "0"
    else if I64.beq d 1 then "1"
    else if I64.beq d 2 then "2"
    else if I64.beq d 3 then "3"
    else if I64.beq d 4 then "4"
    else if I64.beq d 5 then "5"
    else if I64.beq d 6 then "6"
    else if I64.beq d 7 then "7"
    else if I64.beq d 8 then "8"
    else if I64.beq d 9 then "9"
    else if I64.beq d 10 then "a"
    else if I64.beq d 11 then "b"
    else if I64.beq d 12 then "c"
    else if I64.beq d 13 then "d"
    else if I64.beq d 14 then "e"
    else "f"

def hex16 (n : I64) : String := hex n 16

def hex8 (n : I64) : String := hex n 8

def hex4 (n : I64) : String := hex n 4

def dec (n : I64) : String := I64.to_string n

def file_class (cls : I64) : String :=
    if I64.beq cls 1 then "ELF32" else if I64.beq cls 2 then "ELF64" else "ELF?"

def data_encoding (e : Endian) : String :=
    match e {
        Endian.little => "2's complement, little endian",
        Endian.big => "2's complement, big endian",
    }

def file_type_name (t : I64) : String :=
    if I64.beq t 0 then "NONE"
    else if I64.beq t 1 then "REL (Relocatable file)"
    else if I64.beq t 2 then "EXEC (Executable file)"
    else if I64.beq t 3 then "DYN (Shared object file)"
    else if I64.beq t 4 then "CORE (Core file)"
    else dec t

def machine_name (m : I64) : String :=
    if I64.beq m 0 then "None"
    else if I64.beq m 3 then "Intel 80386"
    else if I64.beq m 8 then "MIPS"
    else if I64.beq m 20 then "PowerPC"
    else if I64.beq m 40 then "ARM"
    else if I64.beq m 62 then "Advanced Micro Devices X86-64"
    else if I64.beq m 183 then "AArch64"
    else if I64.beq m 243 then "RISC-V"
    else dec m

def section_type_name (t : I64) : String :=
    if I64.beq t 0 then "NULL"
    else if I64.beq t 1 then "PROGBITS"
    else if I64.beq t 2 then "SYMTAB"
    else if I64.beq t 3 then "STRTAB"
    else if I64.beq t 4 then "RELA"
    else if I64.beq t 8 then "NOBITS"
    else if I64.beq t 9 then "REL"
    else if I64.beq t 11 then "DYNSYM"
    else if I64.beq t 14 then "INIT_ARRAY"
    else if I64.beq t 15 then "FINI_ARRAY"
    else if I64.beq t 16 then "PREINIT_ARRAY"
    else if I64.beq t 17 then "GROUP"
    else if I64.beq t 18 then "SYMTAB_SHNDX"
    else dec t

def program_type_name (t : I64) : String :=
    if I64.beq t 0 then "NULL"
    else if I64.beq t 1 then "LOAD"
    else if I64.beq t 2 then "DYNAMIC"
    else if I64.beq t 3 then "INTERP"
    else if I64.beq t 4 then "NOTE"
    else if I64.beq t 5 then "SHLIB"
    else if I64.beq t 6 then "PHDR"
    else if I64.beq t 7 then "TLS"
    else if I64.beq t 0x6474e550 then "GNU_EH_FRAME"
    else if I64.beq t 0x6474e551 then "GNU_STACK"
    else if I64.beq t 0x6474e552 then "GNU_RELRO"
    else dec t

/// `R`/`W`/`E` for the three flag bits a program or section header uses.
def flag_letters (flags : I64) (mask_read : I64) (mask_write : I64) (mask_exec : I64) : String :=
    String.concat
        (if btest flags mask_read then "R" else " ")
        (String.concat
            (if btest flags mask_write then "W" else " ")
            (if btest flags mask_exec then "E" else " "))

/// One bit of `flags`, without bitwise operators (I64 has none): divide and
/// compare the remainder.
def btest (flags : I64) (mask : I64) : Bool :=
    if I64.lt flags mask then false
    else I64.beq (I64.sub flags (I64.mul (I64.div flags mask) mask)) mask

// ─── Output ──────────────────────────────────────────────────────────

def print_lines (ls : List String) : IO Unit :=
    match ls {
        List.empty => IO.pure Unit.unit,
        List.cons l rest => print_line_then l rest
    }

#[terminating]
def print_line_then (l : String) (rest : List String) : IO Unit := do {
    let _ <- IO.println l;
    print_lines rest
}

def header_lines (h : ElfHeader) : List String :=
    [
        "ELF Header:",
        String.concat "  Class:                        " (file_class h.cls),
        String.concat "  Data:                         " (data_encoding h.endian),
        String.concat "  OS/ABI:                       " (dec h.osabi),
        String.concat "  ABI Version:                  " (dec h.abiversion),
        String.concat "  Type:                         " (file_type_name h.file_type),
        String.concat "  Machine:                      " (machine_name h.machine),
        String.concat "  Entry point address:          0x" (hex16 h.entry),
        String.concat "  Start of program headers:     0x" (hex16 h.phoff),
        String.concat "  Start of section headers:     0x" (hex16 h.shoff),
        String.concat "  Flags:                        0x" (hex8 h.flags),
        String.concat "  Size of this header:          " (dec h.ehsize),
        String.concat "  Number of program headers:    " (dec h.phnum),
        String.concat "  Number of section headers:    " (dec h.shnum),
        String.concat "  Section header string table index: " (dec h.shstrndx),
    ]

def program_header_line (p : ProgramHeader) : String :=
    String.concat_all [
        "  ", pad_right 12 (program_type_name p.p_type), " ",
        "0x", hex16 p.offset, " 0x", hex16 p.vaddr,
        " 0x", hex16 p.paddr, " 0x", hex16 p.filesz,
        " 0x", hex16 p.memsz, " ",
        flag_letters p.flags 4 2 1, " 0x", hex16 p.align,
    ]

#[partial]
def program_header_lines (ps : List ProgramHeader) : List String :=
    match ps {
        List.empty => List.empty,
        List.cons p rest =>
            List.cons (program_header_line p) (program_header_lines rest)
    }

def section_line (s : SectionHeader) : String :=
    String.concat_all [
        "  [", pad_left_3 s.index, "] ", pad_right 20 s.name,
        " ", pad_right 10 (section_type_name s.sh_type),
        " 0x", hex16 s.addr, " 0x", hex16 s.offset,
        " 0x", hex8 s.size, " 0x", hex4 s.entsize, " ",
        flag_letters s.flags 2 1 4, "  ", pad_left_3 s.link, "  ", pad_left_3 s.info,
        "  ", dec s.addralign,
    ]

#[partial]
def section_lines (ss : List SectionHeader) : List String :=
    match ss {
        List.empty => List.empty,
        List.cons s rest => List.cons (section_line s) (section_lines rest)
    }

def symbol_line (s : Symbol) : String :=
    String.concat_all [
        "  ", pad_right 28 s.name,
        " 0x", hex16 s.value, "  ", dec s.size, "  ", dec s.info,
        "  ", dec s.other, "  ", dec s.shndx,
    ]

#[partial]
def symbol_lines (ss : List Symbol) : List String :=
    match ss {
        List.empty => List.empty,
        List.cons s rest => List.cons (symbol_line s) (symbol_lines rest)
    }

/// Right-pad to `width` (a display table's fixed columns).
pub def pad_right (width : I64) (s : String) : String :=
    if I64.lt (String.length s) width
    then String.concat s (spaces (width - String.length s))
    else s

def pad_left_3 (n : I64) : String :=
    let s : String := dec n in
    if I64.lt (String.length s) 3 then String.concat (spaces (3 - String.length s)) s else s

#[partial]
def spaces (n : I64) : String :=
    if I64.lt n 1 then "" else String.concat " " (spaces (n - 1))

// ─── The run ─────────────────────────────────────────────────────────

#[cfg {feature := "buf"}]
def run (args : Args) : IO I64 := do {
    if String.is_empty args.file
    then do {
        IO.write_stderr "elfinfo: no file given\nusage: elfinfo <file> [--all]\n";
        return 2
    }
    else do {
        let read <- IO.read_file_buf (Path.path args.file);
        match read {
            Result.err e => do {
                IO.write_stderr (String.concat "elfinfo: "
                    (String.concat args.file (String.concat ": " (String.concat e.message "\n"))));
                return 1
            },
            Result.ok buf => do {
                let bytes : Bytes := Bytes.of_buf (Shared.of buf);
                match parse bytes {
                    Result.err e => do {
                        IO.write_stderr (String.concat "elfinfo: not an ELF file: "
                            (String.concat (dec (ParseError.error_offset e)) "\n"));
                        return 1
                    },
                    Result.ok elf => do {
                        let _u <- print_report args elf;
                        return 0
                    }
                }
            }
        }
    }
}

def print_report (args : Args) (elf : Elf) : IO Unit :=
    // One field pattern is the only way to read four fields out of an
    // affine record: each `elf.field` is a use, so four projections would be
    // four uses, while the pattern is one.
    match elf {
        { header, program_headers, sections, symbols } =>
            print_report_parts args header program_headers sections symbols
    }

def print_report_parts (args : Args) (h : ElfHeader) (phs : List ProgramHeader) (shs : List SectionHeader) (syms : List Symbol) : IO Unit := do {
    if show_headers args then print_lines (header_lines h) else IO.pure Unit.unit;
    if show_program_headers args
    then print_lines (List.cons "Program Headers:" (program_header_lines phs))
    else IO.pure Unit.unit;
    if show_sections args
    then print_lines (List.cons "Section Headers:" (section_lines shs))
    else IO.pure Unit.unit;
    if show_symbols args
    then print_lines (List.cons "Symbols:" (symbol_lines syms))
    else IO.pure Unit.unit
}

#[cfg {feature := "buf"}]
def main (args : List String) : IO I64 := Cli.run spec args decode run
