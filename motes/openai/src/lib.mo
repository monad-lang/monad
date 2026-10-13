// The openai mote's library root -- bare `use openai` resolves here.
//
// Deliberately empty, matching `motes/moose/src/lib.mo`'s own
// precedent: this mote is `types.mo` (the wire-faithful request/
// response types), `tool.mo` (the tool wire types and their
// hand-written nested codecs), and `client.mo` (the HTTP call), and
// declares nothing `pub` here -- a surface in this file would decide
// the mote's API before anyone has.
