// The anthropic mote's library root -- bare `use anthropic` resolves
// here.
//
// Deliberately empty, matching `motes/openai/src/lib.mo`'s own
// precedent: this mote is `types.mo` (the wire-faithful request/
// response types and their hand-written codecs) and `client.mo` (the
// HTTP call), and declares nothing `pub` here -- a surface in this
// file would decide the mote's API before anyone has.
