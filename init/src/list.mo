// List-specific extras beyond the core List type/constructors
// (init/prelude.mo). Re-exported ambiently via init/lib.mo.

/// Get the element at index
def List.get (index : I64) (l : List A) : Option A :=
	// TODO fails to parse properly
	let b := index == 0 in
	if b
	then
	(match l {
		empty => none,
		cons a tail => some a
	})
	else (let b2 := BOrd.gt index 0 in
	if b2
	then match l {
		empty => none,
		cons a tail => List.get (index - 1) tail
	}
	else none)
