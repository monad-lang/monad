// The serde mote's library root -- bare `use serde` resolves here.
//
// Deliberately empty, matching `motes/moose/src/lib.mo`'s own precedent:
// this mote is `format.mo` (the `Serializer`/`Deserializer` classes) and
// `derive.mo` (the generation logic), and declares nothing `pub` here --
// a surface in this file would decide the mote's API before anyone has.
