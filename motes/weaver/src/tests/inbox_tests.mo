/// The turn's inbox: posted notes come back once, in order, and an empty
/// or missing inbox takes nothing.
use weaver::inbox {Inbox.post, Inbox.take}
use std::list {List.length, List.intercalate}

#[test]
def test_inbox_round_trip : IO Bool := do {
    let _ <- Inbox.take Option.none;
    let _ <- Inbox.post Option.none ["first", "second\nline"];
    let got <- Inbox.take Option.none;
    let again <- Inbox.take Option.none;
    IO.pure (String.beq (List.intercalate "|" got) "first|second line" && List.length again == 0)
}

#[test]
def test_inbox_missing_takes_nothing : IO Bool := do {
    let _ <- Inbox.take Option.none;
    let got <- Inbox.take Option.none;
    IO.pure (List.length got == 0)
}
