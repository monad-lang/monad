// The shuttle mote's library root -- bare `use shuttle` resolves here.
//
// Deliberately empty, matching `motes/moose/src/lib.mo`'s own
// precedent: the mote's surface is `message.mo`/`tool.mo`/
// `provider.mo`/`loop.mo`/`wire/*`/`tools/*`/`main.mo`, and declares
// nothing `pub` here -- a surface in this file would decide the
// mote's API before anyone has.
