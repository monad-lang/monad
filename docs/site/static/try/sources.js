// The payload the /try worker hands to the engine, and the only
// implementation of its format on the JS side -- `worker.js` and
// `wasm/web/try_engine_smoke.mjs` both import this, so the served files and
// the engine's parser cannot drift apart.
//
// One record per module, records concatenated with no separator:
//
//   "<path byte length> <source byte length>\n" <path bytes> <source bytes>
//
// The engine slices each body by those lengths, so a source may contain
// newlines, spaces or `#` freely. Lengths also keep the payload free of NUL
// bytes, which matters because a Monad `String` in the web profile is a
// NUL-terminated C string; `try_alloc(len + 1)` relies on that trailing NUL.

const encoder = new TextEncoder();

/// `entries` is `[{ path, source }]` in the order the engine should see
/// them. Returns the bytes to stage in wasm memory.
export function encodeSources(entries) {
  const parts = [];
  let total = 0;
  for (const { path, source } of entries) {
    const pathBytes = encoder.encode(path);
    const sourceBytes = encoder.encode(source);
    const header = encoder.encode(`${pathBytes.length} ${sourceBytes.length}\n`);
    parts.push(header, pathBytes, sourceBytes);
    total += header.length + pathBytes.length + sourceBytes.length;
  }
  const out = new Uint8Array(total);
  let at = 0;
  for (const part of parts) {
    out.set(part, at);
    at += part.length;
  }
  return out;
}
