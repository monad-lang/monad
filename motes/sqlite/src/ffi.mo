// monad-sqlite / ffi -- the SQLite C API, bound by name at link time.
//
// Handle representation: `sqlite3*` and `sqlite3_stmt*` are `Ptr` values.
// `sqlite3_open_v2` and `sqlite3_prepare_v2` return their handle through a
// `T**` out-parameter; `ByteBuf.take_ptr` (std) reads the word back from an
// 8-byte buffer, and `Ptr.minus_one` (init) is `SQLITE_TRANSIENT`. Both are
// `#[native]` APIs, so this file binds only foreign C symbols -- never a
// Monad runtime symbol.
//
// `String` parameters cross as `char*` (the `SSL_set1_host` convention), so
// text binds pass the Monad string directly. `SQLITE_TRANSIENT` makes SQLite
// copy at bind time, so no Monad value has to outlive the call.
//
// Integer literals: there is no `I32` literal, and `I32.add` is not public,
// so combined flags are one `I64.to_i32` of the precomputed value.

#[extern "c"]
def sqlite3_open_v2 (filename : String) (db_out : Ptr) (flags : I32) (vfs : Ptr) : I32

#[extern "c"]
def sqlite3_close_v2 (db : Ptr) : I32

#[extern "c"]
def sqlite3_errmsg (db : Ptr) : Ptr

#[extern "c"]
def sqlite3_errstr (code : I32) : Ptr

#[extern "c"]
def sqlite3_extended_errcode (db : Ptr) : I32

#[extern "c"]
def sqlite3_exec (db : Ptr) (sql : String) (callback : Ptr) (arg : Ptr) (errmsg_out : Ptr) : I32

#[extern "c"]
def sqlite3_prepare_v2 (db : Ptr) (sql : String) (n : I32) (stmt_out : Ptr) (tail : Ptr) : I32

#[extern "c"]
def sqlite3_finalize (stmt : Ptr) : I32

#[extern "c"]
def sqlite3_step (stmt : Ptr) : I32

#[extern "c"]
def sqlite3_bind_null (stmt : Ptr) (idx : I32) : I32

#[extern "c"]
def sqlite3_bind_int64 (stmt : Ptr) (idx : I32) (value : I64) : I32

#[extern "c"]
def sqlite3_bind_double (stmt : Ptr) (idx : I32) (value : F64) : I32

#[extern "c"]
def sqlite3_bind_text (stmt : Ptr) (idx : I32) (text : String) (n : I32)
        (destructor : Ptr) : I32

#[extern "c"]
def sqlite3_bind_blob (stmt : Ptr) (idx : I32) (data : Ptr) (n : I32)
        (destructor : Ptr) : I32

#[extern "c"]
def sqlite3_column_count (stmt : Ptr) : I32

#[extern "c"]
def sqlite3_column_name (stmt : Ptr) (idx : I32) : Ptr

#[extern "c"]
def sqlite3_column_type (stmt : Ptr) (idx : I32) : I32

#[extern "c"]
def sqlite3_column_int64 (stmt : Ptr) (idx : I32) : I64

#[extern "c"]
def sqlite3_column_double (stmt : Ptr) (idx : I32) : F64

#[extern "c"]
def sqlite3_column_text (stmt : Ptr) (idx : I32) : Ptr

#[extern "c"]
def sqlite3_column_blob (stmt : Ptr) (idx : I32) : Ptr

#[extern "c"]
def sqlite3_column_bytes (stmt : Ptr) (idx : I32) : I32

#[extern "c"]
def sqlite3_changes (db : Ptr) : I32

#[extern "c"]
def sqlite3_last_insert_rowid (db : Ptr) : I64

#[extern "c"]
def sqlite3_busy_timeout (db : Ptr) (ms : I32) : I32

// libc, already linked; `n` is declared I64 because the public numeric
// narrowing helpers are module-private and a size_t is a 64-bit register on
// every supported native target.
#[extern "c" {link_name := "strlen"}]
def sqlite_strlen (s : Ptr) : I64

#[extern "c" {link_name := "memcpy"}]
def sqlite_memcpy (dst : Ptr) (src : Ptr) (n : I64) : Ptr

/// SQLITE_OK.
pub def Sqlite.ok : I32 := I64.to_i32 0
/// SQLITE_ROW.
pub def Sqlite.row : I32 := I64.to_i32 100
/// SQLITE_DONE.
pub def Sqlite.done : I32 := I64.to_i32 101

/// SQLITE_OPEN_READWRITE | SQLITE_OPEN_CREATE | SQLITE_OPEN_URI |
/// SQLITE_OPEN_NOMUTEX = 0x0002 | 0x0004 | 0x0040 | 0x8000.
pub def Sqlite.open_flags : I32 := I64.to_i32 32838

/// SQLITE_TRANSIENT: `(sqlite3_destructor_type)-1`. SQLite copies the
/// bound bytes before returning, so no Monad value must stay live until
/// `step`/`finalize`. `Ptr.minus_one` is a zero-argument native, not an
/// I64-to-Ptr conversion.
pub def Sqlite.transient_destructor : Ptr := Ptr.minus_one

// sqlite3_column_type tags.
pub def Sqlite.type_null : I32 := I64.to_i32 5
pub def Sqlite.type_integer : I32 := I64.to_i32 1
pub def Sqlite.type_real : I32 := I64.to_i32 2
pub def Sqlite.type_text : I32 := I64.to_i32 3
pub def Sqlite.type_blob : I32 := I64.to_i32 4
