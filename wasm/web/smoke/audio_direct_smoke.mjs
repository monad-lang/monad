#!/usr/bin/env node
// The imperative sound surface: decoding a file (`fetch` -> `decodeAudioData`
// -> `Sound`) and playing PCM from a `Buf F32`. Usage:
//   node wasm/web/smoke/audio_direct_smoke.mjs <web_audio_direct.wasm> [mode]
//
// `mode` is `ok` (default), `no_body` (the fetch answers nothing) or
// `decode_fail` (`decodeAudioData` rejects with EncodingError). The stub
// fetch and the recording Web Audio stub let the whole two-phase path run
// under Node, which is the only place it is exercised without a browser.
//
// What this pins:
//   1. `probe_pcm` packs 16 F32 frames into a buffer and plays them at a
//      declared 8 kHz -- the source's buffer is 16 samples, so the typed
//      buffer crossed whole (kind and length both honoured).
//   2. `probe_decode` fetches, decodes and plays: the decoded "sound" has
//      one sample per BODY BYTE, which proves the binary body channel
//      (`fetch_len`/`fetch_read_bytes`) carried every zero byte that the
//      NUL-terminated `Fetch.read` would have truncated at.
//   3. Each failure mode is reported, not thrown: `no_body` and
//      `decode:err=EncodingError` are log lines.

import { readFile } from 'node:fs/promises';
import { imports } from '../web.js';
import { host } from '../web_runtime.js';
import { installDocument, fail } from './stub_dom.mjs';
import { installAudio, audioStub } from './stub_audio.mjs';

const path = process.argv[2];
const mode = process.argv[3] || 'ok';
if (!path) {
  console.error('usage: node wasm/web/smoke/audio_direct_smoke.mjs <web_audio_direct.wasm> [mode]');
  process.exit(2);
}

installDocument();

// A body with ZERO bytes in it: 8 leading NULs would stop `Fetch.read`
// (a NUL-terminated Monad String) after the first one, so a decode built on
// it would see an empty file. The byte channel must carry all 24 bytes.
const BODY = new Uint8Array([0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 7, 8, 0, 9, 10, 11, 0, 0, 12, 13]);

globalThis.fetch = async (_url) => ({
  ok: true,
  status: 200,
  headers: { forEach: () => {} },
  arrayBuffer: async () => (mode === 'no_body' ? new ArrayBuffer(0) : BODY.buffer.slice(BODY.byteOffset, BODY.byteOffset + BODY.length)),
});

audioStub.mode = 'full';
if (mode === 'decode_fail') audioStub.decodeFailure = 'EncodingError';
installAudio();

const bytes = await readFile(path);
const { instance } = await WebAssembly.instantiate(bytes, imports);
host.bind(instance);
host.set_root('#app');
instance.exports.monad_main?.(0n);
// The fixture parks its in-flight request in the `Keep` slot; the init export
// creates it, as `oak_mount` does for a runtime state.
instance.exports.probe_init();

const logs = [];
const realLog = console.log.bind(console);
console.log = (...args) => { logs.push(args.join(' ')); };

// Drive an export until it reports an OUTCOME. A two-phase fixture prints
// progress first (`decode:started`, `decode:decoding`, `decode:pending`) and
// only reports once a promise has settled, so the harness turns the event
// loop between calls -- exactly what a browser's frame loop does.
const OUTCOME = /^(pcm_frames=|decode:ok_ms=|decode:err=|decode:no_body|decode:fetch_failed|decode:no_sound|decode:lost_request)/;
const run = async (name, attempts = 10) => {
  logs.length = 0;
  for (let i = 0; i < attempts; i++) {
    await instance.exports[name]();
    if (logs.some((l) => OUTCOME.test(l))) break;
    // Turn the event loop: a fetch/decode promise only settles between
    // synchronous export calls.
    await new Promise((r) => setTimeout(r, 0));
  }
  return logs.slice();
};

// ── PCM ───────────────────────────────────────────────────────────────
const pcmLogs = await run('probe_pcm');
if (!pcmLogs.includes('pcm_frames=16')) fail(`probe_pcm reported ${JSON.stringify(pcmLogs)}`);
const ctx = audioStub.contexts[0];
if (!ctx) fail('probe_pcm opened no AudioContext');
const pcmSource = ctx.sources[ctx.sources.length - 1];
if (!pcmSource || !pcmSource.buffer) fail('probe_pcm started no buffer source');
if (pcmSource.buffer.length !== 16) {
  fail(`PCM buffer has ${pcmSource.buffer.length} samples, want 16`);
}
if (pcmSource.buffer.sampleRate !== 8000) {
  fail(`PCM played at ${pcmSource.buffer.sampleRate} Hz, want 8000`);
}
// The frames are a rounded sine, so the peak must be near 1 (0.5 gain is the
// voice's, not the data's) -- proof the values themselves crossed.
const peak = Math.max(...pcmSource.buffer.getChannelData());
if (Math.abs(peak - 1) > 0.01) fail(`PCM peak is ${peak}, want ~1.0`);

// ── decode ────────────────────────────────────────────────────────────
const decodeLogs = await run('probe_decode');
// Restore the real console BEFORE any report: `fail` and the `ok` line go
// through it, and a harness that captured `console.log` would exit silently.
console.log = realLog;
if (mode === 'no_body') {
  if (!decodeLogs.includes('decode:no_body')) fail(`no-body report: ${JSON.stringify(decodeLogs)}`);
  console.log(`ok: ${path} -> PCM playback and the decode failure path (mode ${mode})`);
  process.exit(0);
}
if (mode === 'decode_fail') {
  if (!decodeLogs.includes('decode:err=EncodingError')) {
    fail(`decode-failure report: ${JSON.stringify(decodeLogs)}`);
  }
  console.log(`ok: ${path} -> PCM playback and the decode failure path (mode ${mode})`);
  process.exit(0);
}

const okLine = decodeLogs.find((l) => l.startsWith('decode:ok_ms='));
if (!okLine) fail(`decode did not succeed: ${JSON.stringify(decodeLogs)}`);
// The stub decodes one sample per body byte at 8 kHz, so the duration is
// BODY.length / 8000 s = 3 ms. A truncated body (8 NULs then a stop) would
// be 1 ms, which is what this catches.
const wantMs = Math.round((BODY.length / 8000) * 1000);
if (okLine !== `decode:ok_ms=${wantMs}`) {
  fail(`decoded duration ${okLine}, want decode:ok_ms=${wantMs} (body ${BODY.length} bytes)`);
}
const played = ctx.sources[ctx.sources.length - 1];
if (!played || !played.buffer) fail('the decoded sound was never played');

console.log(`ok: ${path} -> PCM playback and a whole binary body decoded and played`);
