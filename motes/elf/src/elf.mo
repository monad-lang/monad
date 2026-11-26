/// ELF parsing: the header, the program-header table, the section-header
/// table and the static/dynamic symbol tables, over `parsec::binary`'s
/// `Parser Bytes` combinators.
///
/// Scope: little- and big-endian ELF32 and ELF64, as the header declares
/// them -- one parser parameterised by the file's class (word width) and
/// byte order, not four parsers. `EI_CLASS`/`EI_DATA` are read first and
/// every later field is read through them.
///
/// What it does NOT do: dynamic linking (no `.rela`/PLT resolution, no
/// interpretation of `DT_*`), notes, version definitions, or any
/// interpretation of section contents beyond names and symbols. The
/// `elfinfo` binary prints what is parsed; nothing here executes or
/// relocates anything.
///
/// Every parsed record is `Copy` (integer fields plus a `String`), which
/// keeps the printing code free of borrowed views.
use parsec::core {ParseError, ParseResult}
use parsec::input {Input, Bytes}
use parsec::parser {Parser}
use parsec::binary {
    Endian, byte, bytes_tag, bytes_while, read_u, require, skip,
}
open ParseResult {fail, success}

// ─── Types ───────────────────────────────────────────────────────────

/// The ELF header (`Elf64_Ehdr`; `Elf32_Ehdr` has the same fields with
/// 4-byte words). `cls` is raw `e_ident[EI_CLASS]` so an unknown class is
/// REPORTED rather than silently read as 64-bit.
pub struct ElfHeader {
    cls : I64,
    endian : Endian,
    version : I64,
    osabi : I64,
    abiversion : I64,
    file_type : I64,
    machine : I64,
    entry : I64,
    phoff : I64,
    shoff : I64,
    flags : I64,
    ehsize : I64,
    phentsize : I64,
    phnum : I64,
    shentsize : I64,
    shnum : I64,
    shstrndx : I64,
}

pub instance Copy ElfHeader {
    def copy (h : ElfHeader) : Pair ElfHeader ElfHeader := Pair.pair h h
}

pub struct ProgramHeader {
    p_type : I64,
    flags : I64,
    offset : I64,
    vaddr : I64,
    paddr : I64,
    filesz : I64,
    memsz : I64,
    align : I64,
}

pub instance Copy ProgramHeader {
    def copy (p : ProgramHeader) : Pair ProgramHeader ProgramHeader := Pair.pair p p
}

pub struct SectionHeader {
    index : I64,
    name_index : I64,
    name : String,
    sh_type : I64,
    flags : I64,
    addr : I64,
    offset : I64,
    size : I64,
    link : I64,
    info : I64,
    addralign : I64,
    entsize : I64,
}

/// Clone out of a `Shared` view: every field is `Copy`, so the clone is the
/// value itself. Needed because a section looked up through the shared list
/// handle is a VIEW, and a view cannot be returned by index lookup.
pub instance Clone SectionHeader {
    def clone (x : Shared SectionHeader) : SectionHeader := Shared.get x
}

pub instance Copy SectionHeader {
    def copy (s : SectionHeader) : Pair SectionHeader SectionHeader := Pair.pair s s
}

pub struct Symbol {
    name_index : I64,
    name : String,
    value : I64,
    size : I64,
    info : I64,
    other : I64,
    shndx : I64,
}

pub instance Copy Symbol {
    def copy (s : Symbol) : Pair Symbol Symbol := Pair.pair s s
}

pub struct Elf {
    header : ElfHeader,
    program_headers : List ProgramHeader,
    sections : List SectionHeader,
    symbols : List Symbol,
}

// ─── Header ──────────────────────────────────────────────────────────

/// The word width implied by `EI_CLASS`; 8 when the class is not 1, so an
/// unknown class still reads a full header (and `class_known` reports it).
def word_size (cls : I64) : I64 :=
    if I64.beq cls 1 then 4 else 8

def endian_of (data : I64) : Endian :=
    if I64.beq data 1 then Endian.little else Endian.big

/// `true` for the classes this parser knows (1 = ELF32, 2 = ELF64).
pub def class_known (cls : I64) : Bool :=
    I64.beq cls 1 || I64.beq cls 2

/// `true` for the byte orders this parser knows (1 = little, 2 = big).
pub def endian_known (data : I64) : Bool :=
    I64.beq data 1 || I64.beq data 2

/// `\x7fELF`.
def magic : List U8 := [0x7Fu8, 0x45u8, 0x4Cu8, 0x46u8]

/// The ELF header. `EI_CLASS`/`EI_DATA` are consumed first; every field
/// after them is read through the width and byte order they name.
pub def header : Parser Bytes ElfHeader := do {
    let _ <- bytes_tag magic;
    let cls_b <- byte;
    let data_b <- byte;
    let ver_b <- byte;
    let osabi_b <- byte;
    let abiver_b <- byte;
    let _ <- skip 7;
    let cls : I64 := U8.to_i64 cls_b;
    let data : I64 := U8.to_i64 data_b;
    let ver : I64 := U8.to_i64 ver_b;
    let osabi : I64 := U8.to_i64 osabi_b;
    let abiver : I64 := U8.to_i64 abiver_b;
    let _ <- require (class_known cls) "unsupported ELF class";
    let _ <- require (endian_known data) "unsupported ELF byte order";
    let endian : Endian := endian_of data;
    let w : I64 := word_size cls;
    let file_type <- read_u 2 endian;
    let machine <- read_u 2 endian;
    let version <- read_u 4 endian;
    let entry <- read_u w endian;
    let phoff <- read_u w endian;
    let shoff <- read_u w endian;
    let flags <- read_u 4 endian;
    let ehsize <- read_u 2 endian;
    let phentsize <- read_u 2 endian;
    let phnum <- read_u 2 endian;
    let shentsize <- read_u 2 endian;
    let shnum <- read_u 2 endian;
    let shstrndx <- read_u 2 endian;
    let h : ElfHeader := {
        cls := cls, endian := endian, version := ver, osabi := osabi, abiversion := abiver,
        file_type := file_type, machine := machine, entry := entry,
        phoff := phoff, shoff := shoff, flags := flags, ehsize := ehsize,
        phentsize := phentsize, phnum := phnum,
        shentsize := shentsize, shnum := shnum, shstrndx := shstrndx,
    };
    return h
}

// ─── Fixed-size table walks ──────────────────────────────────────────

def bytes_at (src : Bytes) (off : I64) (size : I64) : Bytes :=
    Bytes.at src off (off + size)

/// Parse up to `n` fixed-size entries starting at absolute `off`, in order.
/// An entry that does not parse ENDS the walk (a truncated table keeps the
/// entries before it -- `readelf` prints what it can) rather than failing
/// the whole file. `p` is APPLIED here, not passed on: a function value is
/// moved by passing it to an owning parameter, so the first use must be a
/// call and only the recursion moves it.
#[partial]
def collect (p : Bytes -> ParseResult Bytes A) (src : Bytes) (off : I64) (size : I64) (i : I64) (n : I64) (acc : List A)
    : List A :=
    if not (I64.lt i n)
    then List.reverse acc
    else
        match p (bytes_at src (off + i * size) size) {
            success _ a => collect p src off size (i + 1) n (List.cons a acc),
            fail _ => List.reverse acc
        }

// ─── Program headers ─────────────────────────────────────────────────

def ph64 (endian : Endian) : Parser Bytes ProgramHeader := do {
    let p_type <- read_u 4 endian;
    let flags <- read_u 4 endian;
    let offset <- read_u 8 endian;
    let vaddr <- read_u 8 endian;
    let paddr <- read_u 8 endian;
    let filesz <- read_u 8 endian;
    let memsz <- read_u 8 endian;
    let align <- read_u 8 endian;
    let p : ProgramHeader := {
        p_type := p_type, flags := flags, offset := offset, vaddr := vaddr,
        paddr := paddr, filesz := filesz, memsz := memsz, align := align,
    };
    return p
}

def ph32 (endian : Endian) : Parser Bytes ProgramHeader := do {
    let p_type <- read_u 4 endian;
    let offset <- read_u 4 endian;
    let vaddr <- read_u 4 endian;
    let paddr <- read_u 4 endian;
    let filesz <- read_u 4 endian;
    let memsz <- read_u 4 endian;
    let flags <- read_u 4 endian;
    let align <- read_u 4 endian;
    let p : ProgramHeader := {
        p_type := p_type, flags := flags, offset := offset, vaddr := vaddr,
        paddr := paddr, filesz := filesz, memsz := memsz, align := align,
    };
    return p
}

pub def program_header (w : I64) (endian : Endian) : Parser Bytes ProgramHeader :=
    if I64.beq w 8 then ph64 endian else ph32 endian

// ─── Section headers ─────────────────────────────────────────────────

def sh64 (endian : Endian) : Parser Bytes SectionHeader := do {
    let name_idx <- read_u 4 endian;
    let sh_type <- read_u 4 endian;
    let flags <- read_u 8 endian;
    let addr <- read_u 8 endian;
    let offset <- read_u 8 endian;
    let size <- read_u 8 endian;
    let link <- read_u 4 endian;
    let info <- read_u 4 endian;
    let addralign <- read_u 8 endian;
    let entsize <- read_u 8 endian;
    let s : SectionHeader := {
        index := 0, name_index := name_idx, name := "", sh_type := sh_type, flags := flags,
        addr := addr, offset := offset, size := size, link := link, info := info,
        addralign := addralign, entsize := entsize,
    };
    return s
}

def sh32 (endian : Endian) : Parser Bytes SectionHeader := do {
    let name_idx <- read_u 4 endian;
    let sh_type <- read_u 4 endian;
    let flags <- read_u 4 endian;
    let addr <- read_u 4 endian;
    let offset <- read_u 4 endian;
    let size <- read_u 4 endian;
    let link <- read_u 4 endian;
    let info <- read_u 4 endian;
    let addralign <- read_u 4 endian;
    let entsize <- read_u 4 endian;
    let s : SectionHeader := {
        index := 0, name_index := name_idx, name := "", sh_type := sh_type, flags := flags,
        addr := addr, offset := offset, size := size, link := link, info := info,
        addralign := addralign, entsize := entsize,
    };
    return s
}

pub def section_header (w : I64) (endian : Endian) : Parser Bytes SectionHeader :=
    if I64.beq w 8 then sh64 endian else sh32 endian

// ─── Symbols ─────────────────────────────────────────────────────────

def sym64 (endian : Endian) : Parser Bytes Symbol := do {
    let name_idx <- read_u 4 endian;
    let info <- read_u 1 endian;
    let other <- read_u 1 endian;
    let shndx <- read_u 2 endian;
    let value <- read_u 8 endian;
    let size <- read_u 8 endian;
    let s : Symbol := {
        name_index := name_idx, name := "", value := value, size := size, info := info,
        other := other, shndx := shndx,
    };
    return s
}

def sym32 (endian : Endian) : Parser Bytes Symbol := do {
    let name_idx <- read_u 4 endian;
    let value <- read_u 4 endian;
    let size <- read_u 4 endian;
    let info <- read_u 1 endian;
    let other <- read_u 1 endian;
    let shndx <- read_u 2 endian;
    let s : Symbol := {
        name_index := name_idx, name := "", value := value, size := size, info := info,
        other := other, shndx := shndx,
    };
    return s
}

pub def symbol (w : I64) (endian : Endian) : Parser Bytes Symbol :=
    if I64.beq w 8 then sym64 endian else sym32 endian

// ─── Names ───────────────────────────────────────────────────────────

/// The NUL-terminated string at `idx` in the string table at
/// `[tab_off, tab_off + tab_size)`; `""` for an index outside it.
def name_at (src : Bytes) (tab_off : I64) (tab_size : I64) (idx : I64) : String :=
    if I64.lt idx 0 || Bool.not (I64.lt idx tab_size)
    then ""
    else
        let span : Bytes := Bytes.at src (tab_off + idx) (tab_off + tab_size) in
        match Parser.run_p (bytes_while is_not_nul) span {
            success _ out => span_text out,
            fail _ => ""
        }

/// The span's own bytes as text -- a helper so the `success` payload binder
/// (typed by the datatype's `O`, hence affine) is used once.
def span_text (span : Bytes) : String :=
    Bytes.text span (Input.input_len span)

def is_not_nul (b : U8) : Bool :=
    Bool.not (U8.beq b 0u8)

#[partial]
def name_sections (src : Bytes) (sections : List SectionHeader) (off : I64) (size : I64) : List SectionHeader :=
    match sections {
        List.empty => List.empty,
        List.cons s rest =>
            let named : SectionHeader := { s with name := name_at src off size s.name_index } in
            List.cons named (name_sections src rest off size)
    }

#[partial]
def name_symbols (src : Bytes) (syms : List Symbol) (off : I64) (size : I64) : List Symbol :=
    match syms {
        List.empty => List.empty,
        List.cons s rest =>
            let named : Symbol := { s with name := name_at src off size s.name_index } in
            List.cons named (name_symbols src rest off size)
    }

#[partial]
def index_sections (ss : List SectionHeader) (i : I64) : List SectionHeader :=
    match ss {
        List.empty => List.empty,
        List.cons s rest => List.cons ({ s with index := i }) (index_sections rest (i + 1))
    }

/// `SHT_SYMTAB` (2) and `SHT_DYNSYM` (11) are the two symbol tables.
def is_symbol_table (s : SectionHeader) : Bool :=
    I64.beq s.sh_type 2 || I64.beq s.sh_type 11

// ─── Random access into the section table ───────────────────────────
//
// The section list is AFFINE (`List` is not `Copy`) and the file needs it
// three times: for the header's own table, for section names, and for each
// symbol table's linked string table. Rather than share one list through
// borrowed views, the table is simply RE-PARSED -- it is a few dozen
// fixed-size entries over a buffer that is already in memory, and a fresh
// walk keeps every value owned.

def parse_sections (src : Bytes) (h : ElfHeader) (w : I64) : List SectionHeader :=
    collect (Parser.run_p (section_header w h.endian)) src h.shoff h.shentsize 0 h.shnum List.empty

/// The `i`-th section header (positionally -- `sh_index` is not known until
/// `index_sections` runs, and a truncated table simply has fewer).
#[partial]
def nth_section (sections : List SectionHeader) (i : I64) (want : I64) : Option SectionHeader :=
    match sections {
        List.empty => Option.none,
        List.cons s rest =>
            if I64.beq i want then Option.some s else nth_section rest (i + 1) want
    }

/// The `[offset, size)` of the string table a section index names.
def strtab_range (src : Bytes) (h : ElfHeader) (w : I64) (idx : I64) : Pair I64 I64 :=
    match nth_section (parse_sections src h w) 0 idx {
        Option.some s => section_range s,
        Option.none => Pair.pair 0 0
    }

/// A section's `[offset, size)` -- a helper so the `Option` payload binder
/// (typed by the datatype's parameter, hence affine) is used once.
def section_range (s : SectionHeader) : Pair I64 I64 :=
    Pair.pair s.offset s.size

// ─── Symbols ────────────────────────────────────────────────────────

#[partial]
def symbols_in (src : Bytes) (h : ElfHeader) (w : I64) (shs : List SectionHeader) : List Symbol :=
    match shs {
        List.empty => List.empty,
        List.cons s rest =>
            List.append (symbols_for src h w s) (symbols_in src h w rest)
    }

def symbols_for (src : Bytes) (h : ElfHeader) (w : I64) (s : SectionHeader) : List Symbol :=
    if is_symbol_table s then symbols_of_section src h w s else List.empty

/// The symbols of one symbol-table section: `sh_size / sh_entsize` entries,
/// named through the string table its `sh_link` names.
def symbols_of_section (src : Bytes) (h : ElfHeader) (w : I64) (s : SectionHeader) : List Symbol :=
    if I64.beq s.entsize 0
    then List.empty
    else
        let n : I64 := I64.div s.size s.entsize in
        let raws : List Symbol :=
            collect (Parser.run_p (symbol w h.endian)) src s.offset s.entsize 0 n List.empty in
        match strtab_range src h w s.link {
            Pair.pair off size => name_symbols src raws off size
        }

// ─── The whole file ──────────────────────────────────────────────────

/// Parse a whole ELF image. The header fails the parse; a truncated table
/// ENDS a walk instead (the entries before the truncation are kept), which
/// is what lets `elfinfo` describe a file whose section table claims more
/// entries than the file holds.
pub def parse (src : Bytes) : Result ParseError Elf :=
    match Parser.run_p header src {
        fail e => Result.err e,
        success _ h => parse_tables src h
    }

def parse_tables (src : Bytes) (h : ElfHeader) : Result ParseError Elf :=
    let w : I64 := word_size h.cls in
    let phs : List ProgramHeader :=
        collect (Parser.run_p (program_header w h.endian)) src h.phoff h.phentsize 0 h.phnum List.empty in
    match strtab_range src h w h.shstrndx {
        Pair.pair off size =>
            finish_elf src h w phs (name_sections src (index_sections (parse_sections src h w) 0) off size)
    }

def finish_elf (src : Bytes) (h : ElfHeader) (w : I64) (phs : List ProgramHeader) (sections : List SectionHeader)
    : Result ParseError Elf :=
    let syms : List Symbol := symbols_in src h w (index_sections (parse_sections src h w) 0) in
    let e : Elf := {
        header := h, program_headers := phs, sections := sections, symbols := syms,
    } in
    Result.ok e
