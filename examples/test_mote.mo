#![mote { name := "test_mote", deps := [example] }]

use example::greet {greet}

#[test]
def test_mote_greet : Bool :=
  greet "World" == "Hello, World!"

#[test]
def test_mote_greet_empty : Bool :=
  greet "" == "Hello, !"
