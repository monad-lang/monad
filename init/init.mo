// Init module

use io
use math

@[native num_add]
def I64.add (a b : I64) : I64

infix (+) := I64.add

class From T A {
 def from (t: T): A
}

