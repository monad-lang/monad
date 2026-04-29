// Init module

use io
use number

infix (+) := I64.add

class From T A {
 def from (t: T): A
}
