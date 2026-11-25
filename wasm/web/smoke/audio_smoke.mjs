#!/usr/bin/env node
// Sound and audio: `Command.beep`/`Command.hit`/`Command.silence` from an
// Oak update, and `<audio>` transport control by selector. Usage:
//   node wasm/web/smoke/audio_smoke.mjs <oak_sound.wasm> [mode]
//
// The recording Web Audio stub (`stub_audio.mjs`) stands in for the browser:
// it exposes the real `web_runtime.js` host, records every node call, and
// answers `decodeAudioData` deterministically. `mode` is 'full' (default),
// 'none' (no AudioContext) or 'blocked-play' (the autoplay policy).
//
// What this pins:
//   1. A click does NOT open a context: `Command.beep` is the first thing
//      that needs one, so an app that never plays a sound never asks.
//   2. The first beep opens exactly ONE context, resumes it (the click was
//      the gesture), and schedules one oscillator through a gain whose
//      envelope ramps up then to zero, into the master gain.
//   3. A second beep reuses that context -- no second `AudioContext`.
//   4. `Command.hit` schedules a buffer source through a lowpass filter.
//   5. `Command.silence` takes the master gain to 0.
//   6. `MediaCmd.play`/`pause` reach the `<audio>` element the view mounted.
//   7. `direct_probe` shows the imperative API's state/resume/position.

import { readFile } from 'node:fs/promises';
import { imports } from '../web.js';
import { host } from '../web_runtime.js';
import { installDocument, body, fail } from './stub_dom.mjs';
import { installAudio, audioStub, mediaStub } from './stub_audio.mjs';

const path = process.argv[2];
const mode = process.argv[3] || 'full';
if (!path) {
  console.error('usage: node wasm/web/smoke/audio_smoke.mjs <oak_sound.wasm> [mode]');
  process.exit(2);
}

installDocument();
audioStub.mode = mode;
installAudio();

function byId(id) {
  const walk = (n) => {
    if (n.attrs && n.attrs.id === id) return n;
    for (const c of n.childNodes) {
      const found = walk(c);
      if (found) return found;
    }
    return null;
  };
  return walk(body);
}
const count = () => byId('count')?.textContent;

const bytes = await readFile(path);
const { instance } = await WebAssembly.instantiate(bytes, imports);
host.bind(instance);
host.set_root('#app');

// ── nothing opened a context just by mounting ─────────────────────────
instance.exports.oak_mount();
if (audioStub.contexts.length !== 0) {
  fail(`mount opened ${audioStub.contexts.length} AudioContext(s); it must open none`);
}
if (!byId('track')) fail('the view mounted no <audio id="track">');
if (count() !== '0') fail(`initial count is ${count()}`);

// ── a click beeps: one context, resumed, one voice through a master gain ──
const noAudio = audioStub.mode === 'none';
const beepBtn = byId('beep');
if (!beepBtn) fail('no #beep button');
beepBtn.fire('click');
// `dispatch` resumes on the event itself, before the batch folds.
instance.exports.oak_tick();
if (count() !== '1') fail(`after a beep the count is ${count()}`);
if (noAudio) {
  // No Web Audio at all: the update still folded and the sound is a no-op.
  if (audioStub.contexts.length !== 0) fail('a context appeared without AudioContext');
  console.log(`ok: ${path} -> oak Command.beep/hit/silence and MediaCmd transport (mode ${mode})`);
  process.exit(0);
}
if (audioStub.contexts.length !== 1) {
  fail(`the first beep opened ${audioStub.contexts.length} contexts, want 1`);
}
const ctx = audioStub.contexts[0];
if (ctx.state !== 'running') fail(`context state is ${ctx.state}, want running (the click is a gesture)`);
if (ctx.oscillators.length !== 1) fail(`scheduled ${ctx.oscillators.length} oscillators, want 1`);
const osc = ctx.oscillators[0];
if (osc.type !== 'square') fail(`oscillator type is ${osc.type}, want square (Wave.square)`);
if (osc.frequency.value !== 440) fail(`oscillator frequency is ${osc.frequency.value}, want 440`);
if (!osc.started) fail('the oscillator was never started');
if (!osc.stopped) fail('the oscillator never scheduled its own stop');

// The envelope: up to the peak, back to zero.
const envelope = ctx.calls.filter((c) => String(c[0]).startsWith('gain#') && c[0].endsWith('.gain.linearRampToValueAtTime'));
const peaks = envelope.map((c) => c[1]);
if (!peaks.includes(0.4)) fail(`envelope peaks ${JSON.stringify(peaks)}, want 0.4 in it`);
if (peaks[peaks.length - 1] !== 0) fail(`envelope never releases to zero: ${JSON.stringify(peaks)}`);

// A second beep reuses the context.
beepBtn.fire('click');
instance.exports.oak_tick();
if (count() !== '2') fail(`after two beeps the count is ${count()}`);
if (audioStub.contexts.length !== 1) {
  fail(`the second beep opened ${audioStub.contexts.length} contexts, want the same one`);
}

// ── a hit is a filtered noise burst ───────────────────────────────────
const before = ctx.sources.length;
byId('hit').fire('click');
instance.exports.oak_tick();
if (ctx.sources.length !== before + 1) fail(`the hit scheduled ${ctx.sources.length - before} sources, want 1`);
const src = ctx.sources[ctx.sources.length - 1];
if (!src.buffer) fail('the hit source has no buffer');
if (!src.started) fail('the hit source never started');
const filterCalls = ctx.calls.filter((c) => c[0] === 'filter.connect');
if (!filterCalls.length) fail('the hit did not route through a lowpass filter');
const freqCalls = ctx.calls.filter((c) => String(c[0]).endsWith('filter#1.frequency.setValueAtTime'));
if (freqCalls.length && freqCalls[freqCalls.length - 1][1] !== 900) {
  fail(`the lowpass is at ${freqCalls[freqCalls.length - 1][1]}, want 900`);
}

// ── silence takes the master gain to zero ─────────────────────────────
// The master gain is `gain#1` (the first node `audio_open` makes) and
// `audio_set_master` sets its `.value` directly, which the stub records.
const masterBefore = ctx.calls.filter((c) => c[0] === 'gain#1.gain.value=').length;
byId('silence').fire('click');
instance.exports.oak_tick();
const masterSets = ctx.calls.filter((c) => c[0] === 'gain#1.gain.value=');
if (masterSets.length === masterBefore) fail('Command.silence did not touch the master gain');
if (masterSets[masterSets.length - 1][1] !== 0) {
  fail(`Command.silence left the master gain at ${masterSets[masterSets.length - 1][1]}, want 0`);
}

// ── media transport reaches the element the view mounted ──────────────
const track = mediaStub.elements.find((e) => e.node.attrs && e.node.attrs.id === 'track');
if (!track) fail('the <audio id="track"> was not instrumented');
if (track.playCalls !== 0) fail('the track played before any play command');
byId('play').fire('click');
instance.exports.oak_tick();
if (track.playCalls !== 1) fail(`#play reached the element ${track.playCalls} times, want 1`);
if (audioStub.mode === 'blocked-play') {
  // The policy refused: the call was made, the element stayed paused, and
  // that is the whole point -- the app can show a "tap to play".
  if (!track.paused) fail('a blocked play() reported playing');
} else if (track.paused) {
  fail('the element is still paused after MediaCmd.play');
}
byId('pause').fire('click');
instance.exports.oak_tick();
if (track.pauseCalls !== 1) fail(`#pause reached the element ${track.pauseCalls} times, want 1`);
if (!track.paused) fail('the element is still playing after MediaCmd.pause');

// ── the imperative API ────────────────────────────────────────────────
const logs = [];
const realLog = console.log.bind(console);
console.log = (...args) => { logs.push(args.join(' ')); };
instance.exports.direct_probe();
console.log = realLog;
if (!logs.some((l) => l === 'position_ms=0')) fail(`imperative position read ${JSON.stringify(logs)}`);
if (audioStub.mode === 'none') {
  if (!logs.some((l) => l === 'state=suspended')) fail(`no-AudioContext state: ${JSON.stringify(logs)}`);
} else {
  if (!logs.some((l) => l === 'state=running')) fail(`imperative state: ${JSON.stringify(logs)}`);
  if (!logs.some((l) => l === 'after_resume=running')) fail(`imperative resume: ${JSON.stringify(logs)}`);
}

console.log(`ok: ${path} -> oak Command.beep/hit/silence and MediaCmd transport (mode ${mode})`);
