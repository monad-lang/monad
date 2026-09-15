/// Show class

pub class Show A {
    def show : A -> String
}

pub instance Show String {
    def show (s: String) : String := s
}

pub instance Show I64 {
    def show (n: I64) : String := I64.to_string n
}

pub instance Show Bool {
    def show (b: Bool) : String :=
        if b then "true" else "false"
}
