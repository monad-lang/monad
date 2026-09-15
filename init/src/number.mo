
/// Number types and operations

// I8

#[native i8_add]
def I8.add (a b : I8) : I8

#[native i8_sub]
pub def I8.sub (a b : I8) : I8

#[native i8_mul]
def I8.mul (a b : I8) : I8

#[native i8_div]
def I8.div (a b : I8) : I8

#[native i8_eq]
pub def I8.beq (a b : I8) : Bool

#[native i8_lt]
def I8.lt (a b : I8) : Bool

#[native i8_gt]
pub def I8.gt (a b : I8) : Bool

#[native i8_to_string]
pub def I8.to_string (a : I8) : String

instance Add I8 {
	def add (a b : I8) : I8 := I8.add a b
}

pub instance Sub I8 {
	def sub (a b : I8) : I8 := I8.sub a b
}

instance HMul I8 I8 I8 {
	def mul (a b : I8) : I8 := I8.mul a b
}

instance Div I8 {
	def div (a b : I8) : I8 := I8.div a b
}

pub instance BEq I8 {
	def beq (a b : I8) : Bool := I8.beq a b
}

pub instance BOrd I8 {
	def lt (a b : I8) : Bool := I8.lt a b
	def gt (a b : I8) : Bool := I8.gt a b
}

pub instance ToString I8 {
	def to_string (a : I8) : String := I8.to_string a
}

// I16

#[native i16_add]
def I16.add (a b : I16) : I16

#[native i16_sub]
pub def I16.sub (a b : I16) : I16

#[native i16_mul]
def I16.mul (a b : I16) : I16

#[native i16_div]
def I16.div (a b : I16) : I16

#[native i16_eq]
pub def I16.beq (a b : I16) : Bool

#[native i16_lt]
def I16.lt (a b : I16) : Bool

#[native i16_gt]
pub def I16.gt (a b : I16) : Bool

#[native i16_to_string]
pub def I16.to_string (a : I16) : String

instance Add I16 {
	def add (a b : I16) : I16 := I16.add a b
}

pub instance Sub I16 {
	def sub (a b : I16) : I16 := I16.sub a b
}

instance HMul I16 I16 I16 {
	def mul (a b : I16) : I16 := I16.mul a b
}

instance Div I16 {
	def div (a b : I16) : I16 := I16.div a b
}

pub instance BEq I16 {
	def beq (a b : I16) : Bool := I16.beq a b
}

pub instance BOrd I16 {
	def lt (a b : I16) : Bool := I16.lt a b
	def gt (a b : I16) : Bool := I16.gt a b
}

pub instance ToString I16 {
	def to_string (a : I16) : String := I16.to_string a
}

// I32

#[native i32_add]
def I32.add (a b : I32) : I32

#[native i32_sub]
pub def I32.sub (a b : I32) : I32

#[native i32_mul]
def I32.mul (a b : I32) : I32

#[native i32_div]
def I32.div (a b : I32) : I32

#[native i32_eq]
pub def I32.beq (a b : I32) : Bool

#[native i32_lt]
def I32.lt (a b : I32) : Bool

#[native i32_gt]
pub def I32.gt (a b : I32) : Bool

#[native i32_to_string]
pub def I32.to_string (a : I32) : String

instance Add I32 {
	def add (a b : I32) : I32 := I32.add a b
}

pub instance Sub I32 {
	def sub (a b : I32) : I32 := I32.sub a b
}

instance HMul I32 I32 I32 {
	def mul (a b : I32) : I32 := I32.mul a b
}

instance Div I32 {
	def div (a b : I32) : I32 := I32.div a b
}

pub instance BEq I32 {
	def beq (a b : I32) : Bool := I32.beq a b
}

pub instance BOrd I32 {
	def lt (a b : I32) : Bool := I32.lt a b
	def gt (a b : I32) : Bool := I32.gt a b
}

pub instance ToString I32 {
	def to_string (a : I32) : String := I32.to_string a
}

// I64

#[native i64_add]
def I64.add (a b : I64) : I64

#[native i64_sub]
pub def I64.sub (a b : I64) : I64

#[native i64_mul]
def I64.mul (a b : I64) : I64

#[native i64_div]
def I64.div (a b : I64) : I64

#[native i64_lt]
def I64.lt (a b : I64) : Bool

#[native i64_gt]
pub def I64.gt (a b : I64) : Bool

#[native i64_to_u64]
def I64.to_u64 (a : I64) : U64

#[native i64_to_u32]
def I64.to_u32 (a : I64) : U32

#[native i64_eq]
pub def I64.beq (a b : I64) : Bool

#[native i64_to_string]
pub def I64.to_string (a : I64) : String

/// Arithmetic negation. Canonical home for what `lang/json.mo` and
/// `lang/toml.mo` each had as their own `neg_i64`/`Toml.neg_i64`
/// (duplicated only because top-level names are not file-scoped).
def I64.neg (n : I64) : I64 := 0 - n

instance Add I64 {
	def add (a b : I64) : I64 := I64.add a b
}

pub instance Sub I64 {
	// `I64.sub`, NOT `a - b`: `infix (-) := Sub.sub` (init/prelude.mo), so
	// spelling this with the operator makes it call itself.
	def sub (a b : I64) : I64 := I64.sub a b
}

instance HMul I64 I64 I64 {
	def mul (a b : I64) : I64 := I64.mul a b
}

instance Div I64 {
	def div (a b : I64) : I64 := I64.div a b
}

pub instance BEq I64 {
	def beq (a b : I64) : Bool := I64.beq a b
}

pub instance BOrd I64 {
	def lt (a b : I64) : Bool := I64.lt a b
	def gt (a b : I64) : Bool := I64.gt a b
}

pub instance ToString I64 {
  def to_string (a : I64) : String := I64.to_string a
}

instance Hashable I64 {
  def hash (a : I64) : U64 := I64.to_u64 a
}

// U8

#[native u8_add]
def U8.add (a b : U8) : U8

#[native u8_sub]
pub def U8.sub (a b : U8) : U8

#[native u8_mul]
def U8.mul (a b : U8) : U8

#[native u8_div]
def U8.div (a b : U8) : U8

#[native u8_eq]
pub def U8.beq (a b : U8) : Bool

#[native u8_to_u64]
def U8.to_u64 (a : U8) : U64

#[native u8_to_u32]
def U8.to_u32 (a : U8) : U32

#[native u8_lt]
def U8.lt (a b : U8) : Bool

#[native u8_gt]
pub def U8.gt (a b : U8) : Bool

#[native u8_to_string]
pub def U8.to_string (a : U8) : String

instance Add U8 {
	def add (a b : U8) : U8 := U8.add a b
}

pub instance Sub U8 {
	def sub (a b : U8) : U8 := U8.sub a b
}

instance HMul U8 U8 U8 {
	def mul (a b : U8) : U8 := U8.mul a b
}

instance Div U8 {
	def div (a b : U8) : U8 := U8.div a b
}

pub instance BEq U8 {
	def beq (a b : U8) : Bool := U8.beq a b
}

pub instance BOrd U8 {
	def lt (a b : U8) : Bool := U8.lt a b
	def gt (a b : U8) : Bool := U8.gt a b
}

pub instance ToString U8 {
	def to_string (a : U8) : String := U8.to_string a
}

// U16

#[native u16_add]
def U16.add (a b : U16) : U16

#[native u16_sub]
pub def U16.sub (a b : U16) : U16

#[native u16_mul]
def U16.mul (a b : U16) : U16

#[native u16_div]
def U16.div (a b : U16) : U16

#[native u16_eq]
pub def U16.beq (a b : U16) : Bool

#[native u16_lt]
def U16.lt (a b : U16) : Bool

#[native u16_gt]
pub def U16.gt (a b : U16) : Bool

#[native u16_to_string]
pub def U16.to_string (a : U16) : String

instance Add U16 {
	def add (a b : U16) : U16 := U16.add a b
}

pub instance Sub U16 {
	def sub (a b : U16) : U16 := U16.sub a b
}

instance HMul U16 U16 U16 {
	def mul (a b : U16) : U16 := U16.mul a b
}

instance Div U16 {
	def div (a b : U16) : U16 := U16.div a b
}

pub instance BEq U16 {
	def beq (a b : U16) : Bool := U16.beq a b
}

pub instance BOrd U16 {
	def lt (a b : U16) : Bool := U16.lt a b
	def gt (a b : U16) : Bool := U16.gt a b
}

pub instance ToString U16 {
	def to_string (a : U16) : String := U16.to_string a
}

// U32

#[native u32_add]
def U32.add (a b : U32) : U32

#[native u32_sub]
pub def U32.sub (a b : U32) : U32

#[native u32_mul]
def U32.mul (a b : U32) : U32

#[native u32_div]
def U32.div (a b : U32) : U32

#[native u32_eq]
pub def U32.beq (a b : U32) : Bool

#[native u32_lt]
def U32.lt (a b : U32) : Bool

#[native u32_gt]
pub def U32.gt (a b : U32) : Bool

#[native u32_to_string]
pub def U32.to_string (a : U32) : String

instance Add U32 {
	def add (a b : U32) : U32 := U32.add a b
}

pub instance Sub U32 {
	def sub (a b : U32) : U32 := U32.sub a b
}

instance HMul U32 U32 U32 {
	def mul (a b : U32) : U32 := U32.mul a b
}

instance Div U32 {
	def div (a b : U32) : U32 := U32.div a b
}

pub instance BEq U32 {
	def beq (a b : U32) : Bool := U32.beq a b
}

pub instance BOrd U32 {
	def lt (a b : U32) : Bool := U32.lt a b
	def gt (a b : U32) : Bool := U32.gt a b
}

pub instance ToString U32 {
	def to_string (a : U32) : String := U32.to_string a
}

#[native u32_and]
def U32.and (a b : U32) : U32

#[native u32_or]
def U32.or (a b : U32) : U32

#[native u32_xor]
def U32.xor (a b : U32) : U32

#[native u32_shl]
def U32.shl (a b : U32) : U32

#[native u32_shr]
def U32.shr (a b : U32) : U32

#[native u32_to_u8]
def U32.to_u8 (a : U32) : U8

def U32.not (a : U32) : U32 := U32.xor a 0xFFFFFFFFu32

def U32.rotr (a n : U32) : U32 :=
	U32.or (U32.shr a n) (U32.shl a (U32.sub 32u32 n))

// U64

#[native u64_add]
def U64.add (a b : U64) : U64

#[native u64_sub]
pub def U64.sub (a b : U64) : U64

#[native u64_mul]
def U64.mul (a b : U64) : U64

#[native u64_div]
def U64.div (a b : U64) : U64

#[native u64_mod]
def U64.mod (a b : U64) : U64

#[native u64_xor]
def U64.xor (a b : U64) : U64

#[native u64_eq]
pub def U64.beq (a b : U64) : Bool

#[native u64_lt]
def U64.lt (a b : U64) : Bool

#[native u64_gt]
pub def U64.gt (a b : U64) : Bool

#[native u64_to_string]
pub def U64.to_string (a : U64) : String

instance Add U64 {
	def add (a b : U64) : U64 := U64.add a b
}

pub instance Sub U64 {
	def sub (a b : U64) : U64 := U64.sub a b
}

instance HMul U64 U64 U64 {
	def mul (a b : U64) : U64 := U64.mul a b
}

instance Div U64 {
  def div (a b : U64) : U64 := U64.div a b
}

instance Hashable U64 {
  def hash (a : U64) : U64 := a
}

pub instance BEq U64 {
	def beq (a b : U64) : Bool := U64.beq a b
}

pub instance BOrd U64 {
	def lt (a b : U64) : Bool := U64.lt a b
	def gt (a b : U64) : Bool := U64.gt a b
}

pub instance ToString U64 {
	def to_string (a : U64) : String := U64.to_string a
}

// F32

#[native f32_add]
def F32.add (a b : F32) : F32

#[native f32_sub]
pub def F32.sub (a b : F32) : F32

#[native f32_mul]
def F32.mul (a b : F32) : F32

#[native f32_div]
def F32.div (a b : F32) : F32

#[native f32_eq]
pub def F32.beq (a b : F32) : Bool

#[native f32_lt]
def F32.lt (a b : F32) : Bool

#[native f32_gt]
pub def F32.gt (a b : F32) : Bool

#[native f32_to_string]
pub def F32.to_string (a : F32) : String

instance Add F32 {
	def add (a b : F32) : F32 := F32.add a b
}

pub instance Sub F32 {
	def sub (a b : F32) : F32 := F32.sub a b
}

instance HMul F32 F32 F32 {
	def mul (a b : F32) : F32 := F32.mul a b
}

instance Div F32 {
	def div (a b : F32) : F32 := F32.div a b
}

pub instance BEq F32 {
	def beq (a b : F32) : Bool := F32.beq a b
}

pub instance BOrd F32 {
	def lt (a b : F32) : Bool := F32.lt a b
	def gt (a b : F32) : Bool := F32.gt a b
}

pub instance ToString F32 {
	def to_string (a : F32) : String := F32.to_string a
}

// F64

#[native f64_add]
def F64.add (a b : F64) : F64

#[native f64_sub]
pub def F64.sub (a b : F64) : F64

#[native f64_mul]
def F64.mul (a b : F64) : F64

#[native f64_div]
def F64.div (a b : F64) : F64

#[native f64_eq]
pub def F64.beq (a b : F64) : Bool

#[native f64_lt]
def F64.lt (a b : F64) : Bool

#[native f64_gt]
pub def F64.gt (a b : F64) : Bool

#[native f64_to_string]
pub def F64.to_string (a : F64) : String

instance Add F64 {
	def add (a b : F64) : F64 := F64.add a b
}

pub instance Sub F64 {
	def sub (a b : F64) : F64 := F64.sub a b
}

instance HMul F64 F64 F64 {
	def mul (a b : F64) : F64 := F64.mul a b
}

instance Div F64 {
	def div (a b : F64) : F64 := F64.div a b
}

pub instance BEq F64 {
	def beq (a b : F64) : Bool := F64.beq a b
}

pub instance BOrd F64 {
	def lt (a b : F64) : Bool := F64.lt a b
	def gt (a b : F64) : Bool := F64.gt a b
}

pub instance ToString F64 {
	def to_string (a : F64) : String := F64.to_string a
}

def nat_to_i64 (n : Nat) : I64 :=
	match n {
		zero => 0,
		succ m => I64.add 1 (nat_to_i64 m)
	}

pub def Nat.to_string (n : Nat) : String := I64.to_string (nat_to_i64 n)
