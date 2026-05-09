
/// String functions

use math

@[native string_eq]
def String.beq (a b : String) : Bool

@[native string_concat]
def String.concat (a b : String) : String

@[native string_length]
def String.length (s : String) : I64

@[native string_get]
def String.get (s : String) (i : I64) : Option U8

@[native string_to_list]
def String.to_list (s : String) : List U8

@[native string_from_list]
def String.from_list (bytes : List U8) : String

instance BEq String {
	def beq (a b : String) : Bool := String.beq a b
}

instance ToString String {
	def to_string (s : String) : String := s
}

instance Add String {
	def add (a b : String) : String := String.concat a b
}

instance Append String {
	def append (a b : String) : String := String.concat a b
}

def String.is_empty (s : String) : Bool :=
	I64.beq (String.length s) 0

// ── List helpers (polymorphic) ──

def List.reverse_append (bytes : List A) (acc : List A) : List A :=
	match bytes {
		empty => acc,
		cons b rest => List.reverse_append rest (List.cons b acc)
	}

def List.reverse (self : List A) : List A :=
	List.reverse_append self List.empty

def List.singleton (a : A) : List A :=
	List.cons a List.empty

// ── List U8 helpers (pattern-only, concrete) ──

def list_starts_with (full : List U8) (prefix : List U8) : Bool :=
	match prefix {
		empty => true,
		cons p_byte p_tail => match full {
			empty => false,
			cons f_byte f_tail =>
				if U8.beq p_byte f_byte
				then list_starts_with f_tail p_tail
				else false
		}
	}

def list_contains (haystack : List U8) (needle : List U8) : Bool :=
	match haystack {
		empty => List.is_empty needle,
		cons _ tail =>
			if list_starts_with haystack needle
			then true
			else list_contains tail needle
	}

// ── Prefix / Suffix ──

def String.starts_with (s : String) (prefix : String) : Bool :=
	list_starts_with (String.to_list s) (String.to_list prefix)

def String.ends_with (s : String) (suffix : String) : Bool :=
	String.starts_with (String.reverse s) (String.reverse suffix)

// ── Repetition ──

def String.repeat (s : String) (n : I64) : String :=
	if I64.beq n 0
	then ""
	else String.concat s (String.repeat s (I64.sub n 1))

// ── Reverse ──

def String.reverse (s : String) : String :=
	String.from_list (List.reverse (String.to_list s))

// ── Search ──

def String.contains (s : String) (sub : String) : Bool :=
	list_contains (String.to_list s) (String.to_list sub)

// ── Trim ──

def is_whitespace_byte (b : U8) : Bool :=
	U8.beq b 32u8 || U8.beq b 9u8 || U8.beq b 10u8 || U8.beq b 13u8

def trim_leading (bytes : List U8) : List U8 :=
	match bytes {
		empty => bytes,
		cons b rest =>
			if is_whitespace_byte b
			then trim_leading rest
			else bytes
	}

def String.trim (s : String) : String :=
	String.from_list (List.reverse (trim_leading (List.reverse (trim_leading (String.to_list s)))))
