
/// Number types and operations

// I8

@[native i8_add]
def I8.add (a b : I8) : I8

@[native i8_sub]
def I8.sub (a b : I8) : I8

@[native i8_mul]
def I8.mul (a b : I8) : I8

@[native i8_div]
def I8.div (a b : I8) : I8

@[native i8_eq]
def I8.beq (a b : I8) : Bool

@[native i8_to_string]
def I8.to_string (a : I8) : String

instance Add I8 {
	def add (a b : I8) : I8 := I8.add a b
}

instance Sub I8 {
	def sub (a b : I8) : I8 := I8.sub a b
}

instance HMul I8 I8 I8 {
	def mul (a b : I8) : I8 := I8.mul a b
}

instance Div I8 {
	def div (a b : I8) : I8 := I8.div a b
}

instance BEq I8 {
	def beq (a b : I8) : Bool := I8.beq a b
}

instance ToString I8 {
	def to_string (a : I8) : String := I8.to_string a
}

// I16

@[native i16_add]
def I16.add (a b : I16) : I16

@[native i16_sub]
def I16.sub (a b : I16) : I16

@[native i16_mul]
def I16.mul (a b : I16) : I16

@[native i16_div]
def I16.div (a b : I16) : I16

@[native i16_eq]
def I16.beq (a b : I16) : Bool

@[native i16_to_string]
def I16.to_string (a : I16) : String

instance Add I16 {
	def add (a b : I16) : I16 := I16.add a b
}

instance Sub I16 {
	def sub (a b : I16) : I16 := I16.sub a b
}

instance HMul I16 I16 I16 {
	def mul (a b : I16) : I16 := I16.mul a b
}

instance Div I16 {
	def div (a b : I16) : I16 := I16.div a b
}

instance BEq I16 {
	def beq (a b : I16) : Bool := I16.beq a b
}

instance ToString I16 {
	def to_string (a : I16) : String := I16.to_string a
}

// I32

@[native i32_add]
def I32.add (a b : I32) : I32

@[native i32_sub]
def I32.sub (a b : I32) : I32

@[native i32_mul]
def I32.mul (a b : I32) : I32

@[native i32_div]
def I32.div (a b : I32) : I32

@[native i32_eq]
def I32.beq (a b : I32) : Bool

@[native i32_to_string]
def I32.to_string (a : I32) : String

instance Add I32 {
	def add (a b : I32) : I32 := I32.add a b
}

instance Sub I32 {
	def sub (a b : I32) : I32 := I32.sub a b
}

instance HMul I32 I32 I32 {
	def mul (a b : I32) : I32 := I32.mul a b
}

instance Div I32 {
	def div (a b : I32) : I32 := I32.div a b
}

instance BEq I32 {
	def beq (a b : I32) : Bool := I32.beq a b
}

instance ToString I32 {
	def to_string (a : I32) : String := I32.to_string a
}

// I64

@[native i64_add]
def I64.add (a b : I64) : I64

@[native i64_sub]
def I64.sub (a b : I64) : I64

@[native i64_mul]
def I64.mul (a b : I64) : I64

@[native i64_div]
def I64.div (a b : I64) : I64

@[native i64_eq]
def I64.beq (a b : I64) : Bool

@[native i64_to_string]
def I64.to_string (a : I64) : String

instance Add I64 {
	def add (a b : I64) : I64 := I64.add a b
}

instance Sub I64 {
	def sub (a b : I64) : I64 := I64.sub a b
}

instance HMul I64 I64 I64 {
	def mul (a b : I64) : I64 := I64.mul a b
}

instance Div I64 {
	def div (a b : I64) : I64 := I64.div a b
}

instance BEq I64 {
	def beq (a b : I64) : Bool := I64.beq a b
}

instance ToString I64 {
	def to_string (a : I64) : String := I64.to_string a
}

// U8

@[native u8_add]
def U8.add (a b : U8) : U8

@[native u8_sub]
def U8.sub (a b : U8) : U8

@[native u8_mul]
def U8.mul (a b : U8) : U8

@[native u8_div]
def U8.div (a b : U8) : U8

@[native u8_eq]
def U8.beq (a b : U8) : Bool

@[native u8_to_string]
def U8.to_string (a : U8) : String

instance Add U8 {
	def add (a b : U8) : U8 := U8.add a b
}

instance Sub U8 {
	def sub (a b : U8) : U8 := U8.sub a b
}

instance HMul U8 U8 U8 {
	def mul (a b : U8) : U8 := U8.mul a b
}

instance Div U8 {
	def div (a b : U8) : U8 := U8.div a b
}

instance BEq U8 {
	def beq (a b : U8) : Bool := U8.beq a b
}

instance ToString U8 {
	def to_string (a : U8) : String := U8.to_string a
}

// U16

@[native u16_add]
def U16.add (a b : U16) : U16

@[native u16_sub]
def U16.sub (a b : U16) : U16

@[native u16_mul]
def U16.mul (a b : U16) : U16

@[native u16_div]
def U16.div (a b : U16) : U16

@[native u16_eq]
def U16.beq (a b : U16) : Bool

@[native u16_to_string]
def U16.to_string (a : U16) : String

instance Add U16 {
	def add (a b : U16) : U16 := U16.add a b
}

instance Sub U16 {
	def sub (a b : U16) : U16 := U16.sub a b
}

instance HMul U16 U16 U16 {
	def mul (a b : U16) : U16 := U16.mul a b
}

instance Div U16 {
	def div (a b : U16) : U16 := U16.div a b
}

instance BEq U16 {
	def beq (a b : U16) : Bool := U16.beq a b
}

instance ToString U16 {
	def to_string (a : U16) : String := U16.to_string a
}

// U32

@[native u32_add]
def U32.add (a b : U32) : U32

@[native u32_sub]
def U32.sub (a b : U32) : U32

@[native u32_mul]
def U32.mul (a b : U32) : U32

@[native u32_div]
def U32.div (a b : U32) : U32

@[native u32_eq]
def U32.beq (a b : U32) : Bool

@[native u32_to_string]
def U32.to_string (a : U32) : String

instance Add U32 {
	def add (a b : U32) : U32 := U32.add a b
}

instance Sub U32 {
	def sub (a b : U32) : U32 := U32.sub a b
}

instance HMul U32 U32 U32 {
	def mul (a b : U32) : U32 := U32.mul a b
}

instance Div U32 {
	def div (a b : U32) : U32 := U32.div a b
}

instance BEq U32 {
	def beq (a b : U32) : Bool := U32.beq a b
}

instance ToString U32 {
	def to_string (a : U32) : String := U32.to_string a
}

// U64

@[native u64_add]
def U64.add (a b : U64) : U64

@[native u64_sub]
def U64.sub (a b : U64) : U64

@[native u64_mul]
def U64.mul (a b : U64) : U64

@[native u64_div]
def U64.div (a b : U64) : U64

@[native u64_eq]
def U64.beq (a b : U64) : Bool

@[native u64_to_string]
def U64.to_string (a : U64) : String

instance Add U64 {
	def add (a b : U64) : U64 := U64.add a b
}

instance Sub U64 {
	def sub (a b : U64) : U64 := U64.sub a b
}

instance HMul U64 U64 U64 {
	def mul (a b : U64) : U64 := U64.mul a b
}

instance Div U64 {
	def div (a b : U64) : U64 := U64.div a b
}

instance BEq U64 {
	def beq (a b : U64) : Bool := U64.beq a b
}

instance ToString U64 {
	def to_string (a : U64) : String := U64.to_string a
}

// F32

@[native f32_add]
def F32.add (a b : F32) : F32

@[native f32_sub]
def F32.sub (a b : F32) : F32

@[native f32_mul]
def F32.mul (a b : F32) : F32

@[native f32_div]
def F32.div (a b : F32) : F32

@[native f32_eq]
def F32.beq (a b : F32) : Bool

@[native f32_to_string]
def F32.to_string (a : F32) : String

instance Add F32 {
	def add (a b : F32) : F32 := F32.add a b
}

instance Sub F32 {
	def sub (a b : F32) : F32 := F32.sub a b
}

instance HMul F32 F32 F32 {
	def mul (a b : F32) : F32 := F32.mul a b
}

instance Div F32 {
	def div (a b : F32) : F32 := F32.div a b
}

instance BEq F32 {
	def beq (a b : F32) : Bool := F32.beq a b
}

instance ToString F32 {
	def to_string (a : F32) : String := F32.to_string a
}

// F64

@[native f64_add]
def F64.add (a b : F64) : F64

@[native f64_sub]
def F64.sub (a b : F64) : F64

@[native f64_mul]
def F64.mul (a b : F64) : F64

@[native f64_div]
def F64.div (a b : F64) : F64

@[native f64_eq]
def F64.beq (a b : F64) : Bool

@[native f64_to_string]
def F64.to_string (a : F64) : String

instance Add F64 {
	def add (a b : F64) : F64 := F64.add a b
}

instance Sub F64 {
	def sub (a b : F64) : F64 := F64.sub a b
}

instance HMul F64 F64 F64 {
	def mul (a b : F64) : F64 := F64.mul a b
}

instance Div F64 {
	def div (a b : F64) : F64 := F64.div a b
}

instance BEq F64 {
	def beq (a b : F64) : Bool := F64.beq a b
}

instance ToString F64 {
	def to_string (a : F64) : String := F64.to_string a
}
