// Init module

pub use id
pub use io
pub use number
pub use math
pub use string

infix (+) := I64.add

class From T A {
 def from (t: T): A
}
