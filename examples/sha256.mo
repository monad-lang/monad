/// Demonstrates std/sha256.mo's SHA-256 implementation.

use io {}
open IO {println}
use std.sha256 {}

#[test]
def test_sha256_hello : Bool :=
  Sha256.hash "hello" == "2cf24dba5fb0a30e26e83b2ac5b9e29e1b161e5c1fa7425e73043362938b9824"

def main (args : List String) : IO Unit :=
  println (Sha256.hash "hello world")
