// The moose mote's library root -- bare `use moose` resolves here.
//
// Deliberately EMPTY, for the reason motes/http/src/lib.mo gives at
// length. This mote is one module (`client.mo`, the HTTP/1.1 client); its
// public surface is `Client.request`, `Client.get`, `Client.post`,
// `Client.put`, `Client.patch`, `Client.request_with` and the
// `*_timeout`/`*_stream` forms, which consumers name directly
// (`use moose::client {Client.request}`) rather than through a second
// index here.
//
// What the file buys is that the mote has a target: `use moose` resolves.
