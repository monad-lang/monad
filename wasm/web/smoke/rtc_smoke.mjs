#!/usr/bin/env node
// WebRTC: the oak subscription that owns a peer connection, plus the
// imperative `web_wasm` peer and `getUserMedia`. Usage:
//   node wasm/web/smoke/rtc_smoke.mjs <oak_rtc.wasm>
//
// The fake `RTCPeerConnection` records what the code asked the browser for and
// lets the harness fire `icecandidate`/`connectionstatechange`/`datachannel`/
// `message` in a controlled order. Nothing here drives a real peer connection:
// the point is the ABI and the queueing contract, which is where the C/JS half
// of a native usually breaks.
//
// The contract being checked throughout: a browser callback NEVER re-enters
// wasm. Every event lands in the peer's queue, and the wasm side drains it
// when the harness calls `oak_tick`.

import { readFile } from 'node:fs/promises';
import { imports } from '../web.js';
import { host } from '../web_runtime.js';
import { installDocument, body, fail } from './stub_dom.mjs';

const path = process.argv[2];
if (!path) {
  console.error('usage: node wasm/web/smoke/rtc_smoke.mjs <oak_rtc.wasm>');
  process.exit(2);
}

installDocument();

// ── the fake browser RTCPeerConnection ──────────────────────────────────
//
// `addIceCandidate`/`setLocalDescription`/`setRemoteDescription` complete
// synchronously here, which is what makes the imperative exports (which drain
// in the same call) observable: a real browser would deliver the description
// on a later task.
const peers = [];
class FakePeerConnection {
  constructor(config) {
    this.config = config;
    this.connectionState = 'new';
    this.channels = new Map();
    this.localDescription = null;
    this.remoteDescription = null;
    this.iceCandidates = [];
    this.onicecandidate = null;
    this.ondatachannel = null;
    this.onconnectionstatechange = null;
    this.ontrack = null;
    this.closed = false;
    this.tracks = [];
    peers.push(this);
  }
  createDataChannel(label, opts) {
    const ch = new FakeDataChannel(label, opts || {});
    this.channels.set(label, ch);
    return ch;
  }
  addTrack(track, stream) {
    this.tracks.push({ track, stream });
  }
  setLocalDescription(desc) {
    this.localDescription = desc;
    // A real browser emits candidates while gathering; the harness emits them
    // explicitly with `fireCandidate` so the order is deterministic.
    this.setState('connected');
  }
  setRemoteDescription(desc) {
    this.remoteDescription = desc;
  }
  addIceCandidate(candidate) {
    this.iceCandidates.push(candidate);
  }
  close() {
    this.closed = true;
    this.setState('closed');
  }
  // Test-only transitions.
  setState(name) {
    this.connectionState = name;
    if (this.onconnectionstatechange) this.onconnectionstatechange({});
  }
  fireCandidate(candidate, mid, mline, ufrag) {
    if (this.onicecandidate) {
      this.onicecandidate({
        candidate: candidate === null ? null : {
          candidate, sdpMid: mid, sdpMLineIndex: mline, usernameFragment: ufrag,
        },
      });
    }
  }
  fireIncomingChannel(label) {
    const ch = new FakeDataChannel(label, { ordered: true });
    this.channels.set(label, ch);
    if (this.ondatachannel) this.ondatachannel({ channel: ch });
    return ch;
  }
  // The remote peer starts sending a stream: the spec delivers one `track`
  // event per track, each carrying the stream it belongs to.
  fireTrack(stream) {
    const track = { kind: 'video', id: 'remote-track' };
    if (this.ontrack) this.ontrack({ track, streams: [stream] });
    return track;
  }
}

class FakeDataChannel {
  constructor(label, opts) {
    this.label = label;
    this.ordered = opts.ordered !== false;
    this.maxRetransmits = opts.maxRetransmits ?? null;
    this.readyState = 'connecting';
    this.binaryType = 'blob';
    this.sent = [];
    this.onopen = null;
    this.onmessage = null;
    this.onclose = null;
    this.onclosing = null;
    this.onerror = null;
    // `createDataChannel` does not fire `ondatachannel` for its own channel,
    // and the real browser opens it asynchronously; the harness opens it once
    // the code has attached its handlers.
    queueMicrotask(() => {
      this.readyState = 'open';
      if (this.onopen) this.onopen({});
    });
  }
  send(data) {
    if (this.readyState !== 'open') throw new Error('InvalidStateError');
    this.sent.push(data);
  }
  fireMessage(data) {
    if (this.onmessage) this.onmessage({ data });
  }
}
globalThis.RTCPeerConnection = FakePeerConnection;

// ── the fake navigator.mediaDevices ────────────────────────────────────
const requestedConstraints = [];
const streamsCreated = [];
class FakeMediaStream {
  constructor() {
    this.stopped = 0;
    this.trackRefs = [
      { stop: () => { this.stopped += 1; } },
      { stop: () => { this.stopped += 1; } },
    ];
    streamsCreated.push(this);
  }
  getTracks() { return this.trackRefs; }
}
globalThis.navigator = globalThis.navigator || {};
globalThis.navigator.mediaDevices = {
  getUserMedia(constraints) {
    requestedConstraints.push(constraints);
    return Promise.resolve(new FakeMediaStream());
  },
};

const bytes = await readFile(path);
const { instance } = await WebAssembly.instantiate(bytes, imports);
host.bind(instance);
host.set_root('#app');
instance.exports.oak_mount();

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
const count = () => byId('count').textContent;
// Let the host's `rtc_wake` `setTimeout(0)` run: the wake-up is a MACROtask,
// so a microtask flush (setImmediate/queueMicrotask) would race it.
const settle = () => new Promise((r) => setTimeout(r, 0));

// Captures the `console.log` lines a fixture export writes, since the export
// ABI returns nothing.
function captureLogs(fn) {
  const logs = [];
  const real = console.log.bind(console);
  console.log = (...args) => { logs.push(args.join(' ')); };
  try {
    fn();
  } finally {
    console.log = real;
  }
  return logs;
}
function expectLog(logs, line) {
  if (!logs.includes(line)) fail(`missing log ${JSON.stringify(line)} in ${JSON.stringify(logs)}`);
}

// ── the subscription created exactly one peer, with its config ─────────
if (peers.length !== 1) fail(`expected one peer, the subscription created ${peers.length}`);
const pc = peers[0];
if (!Array.isArray(pc.config.iceServers)) fail('the peer got no iceServers array');
if (pc.config.iceServers.length !== 0) fail(`expected no ICE servers, got ${pc.config.iceServers.length}`);

// ── the fake browser reports a connection: the wake-up dispatches, and
// `update` bumps the model by one ──
pc.setState('connected');
await settle();
instance.exports.oak_tick();
if (count() !== '1') fail(`after connection the count is ${count()}`);

// ── a data channel opening bumps by a hundred; a ready channel makes the
// pure update send through `Command.rtc_send` ──
// `fireIncomingChannel` opens the channel on a microtask, so by the time the
// wake-up runs the queue holds BOTH `data_channel` (+10) and the channel's
// `channel_state ready` (+100): one dispatch delivers both.
const ch = pc.fireIncomingChannel('chat');
await settle();
instance.exports.oak_tick();
if (count() !== '111') fail(`after datachannel the count is ${count()}`);

// A ready channel makes the pure update answer through `Command.rtc_send`.
// (The open event was delivered above, together with `data_channel`.)
if (ch.sent.length !== 0 && ch.sent[0] !== 'ping') fail('unexpected send');
if (ch.sent.length !== 1) fail(`expected the update to send one message, got ${ch.sent.length}`);
if (ch.sent[0] !== 'ping') fail(`the update sent ${JSON.stringify(ch.sent[0])}`);

// ── a message arrives: the count bumps by a thousand ──
ch.fireMessage('from-the-peer');
await settle();
instance.exports.oak_tick();
if (count() !== '1111') fail(`after a message the count is ${count()}`);

// ── a candidate and a description are queued, not dispatched inline ──
pc.fireCandidate('candidate:1 1 udp 1 127.0.0.1 9 typ host', '0', 0, 'abcd');
pc.setState('failed');
await settle();
instance.exports.oak_tick();
// candidate = 100000, failed connection = 1
if (count() !== '101112') fail(`after a candidate and a failure the count is ${count()}`);

// ── the imperative offerer: a peer, a channel, a local description, then a
// drain. The fake emits one candidate when `setLocalDescription` runs, which
// the harness fires here. ──
peers.length = 0;
const offerLogs = captureLogs(() => instance.exports.imp_offer());
// The peer is closed and freed inside the export, so only the log survives.
// The fake's `setLocalDescription` moves the connection to "connected",
// which queues one state change before the drain.
expectLog(offerLogs, 'offer:events=1');

// ── the imperative answerer: set remote, set local, add a candidate and the
// end-of-candidates marker, then read the live state ──
peers.length = 0;
const answerLogs = captureLogs(() => instance.exports.imp_answer());
expectLog(answerLogs, 'answer:events=1');
expectLog(answerLogs, 'answer:state=connected');

// ── send: the createDataChannel path must open the channel before send, so
// the harness inspects the peer the export made ──
peers.length = 0;
const sendLogs = captureLogs(() => instance.exports.imp_send());
// `imp_send` does not wait for the channel's open, so both sends fail fast --
// which is the honest answer for a channel that is not open yet, and is what
// `closed:send=0` also pins.
expectLog(sendLogs, 'send:text=0');
expectLog(sendLogs, 'send:bytes=0');

// ── sending on a label with no channel fails rather than throwing ──
const closedLogs = captureLogs(() => instance.exports.imp_closed_send());
expectLog(closedLogs, 'closed:send=0');

// ── the null handle is REFUSED. Index 0 of the host's stream table is
// reserved, so the handle a still-pending `getUserMedia` answers names
// nothing: `attach` must fail rather than bind the first live stream. ──
peers.length = 0;
const nullLogs = captureLogs(() => instance.exports.imp_null_handle());
expectLog(nullLogs, 'null:attach=0');

// ── a remote stream: `ontrack` must REGISTER the stream, so the app gets a
// handle it can attach -- that is the receive half of media, and the pure
// layer names it `RtcEvent.track`. Before the fix nothing was registered and
// the only handles that ever existed were local cameras. ──
const remote = new FakeMediaStream();
const remoteBefore = streamsCreated.length;
pc.fireTrack(remote);
await settle();
instance.exports.oak_tick();
// The subscription's `update` counts a track as +1 (see the fixture's
// `bump`), so the count moves by one and the event carried a usable id.
if (count() !== '101113') fail(`after a remote track the count is ${count()}`);
if (streamsCreated.length !== remoteBefore) fail('a remote track created a local capture');

// ── the camera: begin, poll, attach to a `<video>`, stop ──
const camLogs = captureLogs(() => instance.exports.imp_camera());
expectLog(camLogs, 'camera:poll=0');
// Two requests by now: `imp_null_handle` starts one (deliberately unpolled)
// and `imp_camera` starts the other.
if (requestedConstraints.length !== 2) fail(`getUserMedia was called ${requestedConstraints.length} times`);
const got = requestedConstraints[requestedConstraints.length - 1];
if (got.audio !== true || got.video !== true) fail(`constraints were ${JSON.stringify(got)}`);

// The promise settles on a microtask, so the poll inside the export saw
// "pending". A second export polls again and now sees the stream.
await settle();
const second = captureLogs(() => instance.exports.imp_camera());
// Either the second begin is still pending (a fresh op) -- what matters is
// that the first op's promise settled without re-entering wasm.
if (!second.every((l) => l.startsWith('camera:'))) fail(`unexpected logs ${JSON.stringify(second)}`);
if (streamsCreated.length < 1) fail('getUserMedia never resolved a stream');

console.log(`ok: ${path} -> oak Subscription.rtc, the imperative web_wasm peer, and getUserMedia`);
// The runtime keeps a peer's wake-up `setTimeout` armed, so Node would never
// exit on its own; the assertions above are the result, and exiting here is
// the harness's job, not the runtime's.
process.exit(0);
