/// Show class

class Show A {
    def show : A -> String
}

instance Show String {
    def show (s: String) : String := s
}

instance Show I64 {
    def show (n: I64) : String := I64.to_string n
}

instance Show Bool {
    def show (b: Bool) : String :=
        if b then "true" else "false"
}
