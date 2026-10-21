// monad-sql / value -- the backend-agnostic value, row and error types.
//
// A driver (motes/sqlite first) produces `Value`s and `Row`s; the common
// layer never mentions a driver type. `SqlError` is the single error type
// the `Backend` class and the migration runner return.

/// One database value: a parameter or a column.
pub type Value {
    null,
    integer (value : I64),
    real (value : F64),
    text (value : String),
    boolean (value : Bool),
    blob (value : List U8)
}

/// A SQL failure. `backend` carries the driver's own code; the rest are
/// produced by the common layer.
pub type SqlError {
    backend (message : String) (code : I64),
    type_mismatch (message : String),
    migration (message : String),
    io_error (message : String)
}

/// One result row, in column order, with the driver's column names.
pub struct Row {
    cells : List (Pair String Value)
}

/// A query's columns and rows.
pub struct ResultSet {
    columns : List String,
    rows : List Row
}

/// `Result` sequencing without a class constraint.
///
/// Extracted (and namespaced) because a `match` on one `Result A` inside a
/// `match` on a different `Result B` is a checker limitation; every
/// multi-step decoder here goes through this instead.
with SqlResult {
    pub def and_then {E : Type} {A : Type} {B : Type}
            (r : Result E A) (f : A -> Result E B) : Result E B :=
        match r {
            Result.ok a => f a,
            Result.err e => Result.err e
        }
}

with SqlError {
    pub def message (e : SqlError) : String :=
        match e {
            SqlError.backend message code => message,
            SqlError.type_mismatch message => message,
            SqlError.migration message => message,
            SqlError.io_error message => message
        }

    pub def code (e : SqlError) : I64 :=
        match e {
            SqlError.backend _ code => code,
            _ => 0
        }
}

with Value {
    pub def as_i64 (v : Value) : Result SqlError I64 :=
        match v {
            Value.integer n => Result.ok n,
            _ => Result.err (SqlError.type_mismatch "expected an integer value")
        }

    pub def as_f64 (v : Value) : Result SqlError F64 :=
        match v {
            Value.real x => Result.ok x,
            _ => Result.err (SqlError.type_mismatch "expected a real value")
        }

    pub def as_text (v : Value) : Result SqlError String :=
        match v {
            Value.text s => Result.ok s,
            _ => Result.err (SqlError.type_mismatch "expected a text value")
        }

    /// Booleans may arrive as `boolean` (a backend that tags them) or as
    /// `integer` 0/1 (SQLite stores them as integers).
    pub def as_bool (v : Value) : Result SqlError Bool :=
        match v {
            Value.boolean b => Result.ok b,
            Value.integer n => Result.ok (Bool.not (n == 0)),
            _ => Result.err (SqlError.type_mismatch "expected a boolean value")
        }

    pub def as_blob (v : Value) : Result SqlError (List U8) :=
        match v {
            Value.blob bytes => Result.ok bytes,
            _ => Result.err (SqlError.type_mismatch "expected a blob value")
        }
}

/// The cell under `name`, or `none` if the row has no such column.
with Row {
    pub def get (r : Row) (name : String) : Option Value :=
        Row.find_cell name r.cells

    pub def get_i64 (r : Row) (name : String) : Result SqlError I64 :=
        match Row.get r name {
            Option.some v => Value.as_i64 v,
            Option.none => Result.err (SqlError.type_mismatch (String.concat "missing column: " name))
        }

    pub def get_f64 (r : Row) (name : String) : Result SqlError F64 :=
        match Row.get r name {
            Option.some v => Value.as_f64 v,
            Option.none => Result.err (SqlError.type_mismatch (String.concat "missing column: " name))
        }

    pub def get_text (r : Row) (name : String) : Result SqlError String :=
        match Row.get r name {
            Option.some v => Value.as_text v,
            Option.none => Result.err (SqlError.type_mismatch (String.concat "missing column: " name))
        }

    pub def get_bool (r : Row) (name : String) : Result SqlError Bool :=
        match Row.get r name {
            Option.some v => Value.as_bool v,
            Option.none => Result.err (SqlError.type_mismatch (String.concat "missing column: " name))
        }

    pub def get_blob (r : Row) (name : String) : Result SqlError (List U8) :=
        match Row.get r name {
            Option.some v => Value.as_blob v,
            Option.none => Result.err (SqlError.type_mismatch (String.concat "missing column: " name))
        }
}

def Row.cell_value (name : String) (cell : Pair String Value) : Option Value :=
    match cell {
        Pair.pair key value =>
            if String.beq key name then Option.some value else Option.none
    }

def Row.find_cell (name : String) (cells : List (Pair String Value)) : Option Value :=
    match cells {
        List.empty => Option.none,
        List.cons cell rest => Row.find_cell_step name rest (Row.cell_value name cell)
    }

#[terminating]
def Row.find_cell_step (name : String) (rest : List (Pair String Value))
        (found : Option Value) : Option Value :=
    match found {
        Option.some v => Option.some v,
        Option.none => Row.find_cell name rest
    }
