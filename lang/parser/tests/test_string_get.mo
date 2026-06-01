@[test]
def test_string_get : Bool := 
    match String.get "hello" 0 {
        some b => true,
        none => false
    }

@[test]
def test_string_get_char : Bool := 
    match String.get_char "hello" 0 {
        some c => true,
        none => false
    }

@[test]
def test_string_get_char_out_of_bounds : Bool := 
    match String.get_char "hello" 100 {
        some c => false,
        none => true
    }

@[test]
def test_string_get_char_unicode : Bool := 
    match String.get_char "héllo" 0 {
        some c => true,
        none => false
    }
