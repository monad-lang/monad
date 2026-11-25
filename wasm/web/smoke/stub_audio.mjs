// A recording stub of Web Audio for the Node harnesses (CI has no browser).
//
// `installAudio()` installs `AudioContext` + `AudioBuffer` modelled on
// exactly the calls `wasm/web/web_runtime.js` makes, and records them the
// way `stub_gl.mjs` does: each context keeps `calls`, a list of
// `[name, ...args]`, with nodes as stable labels (`osc#1`, `gain#2`) and
// gain automation as `gain#N.gain.<op>`. A harness compares a whole stream
// to a golden, so a change in envelope shape or routing fails loudly.
//
// It also gives every stub `<audio>`/`<video>` node a media-element surface
// (play/pause/seek/volume/mute/loop/readyState/duration), because the
// `media_*` imports drive a real element. `audioStub.mode` selects the
// environment:
//
//   * 'full' (default)  -- Web Audio present, `play()` resolves;
//   * 'none'            -- no `AudioContext` at all (an embedder without it);
//   * 'blocked-play'    -- Web Audio present, but `play()` rejects with
//                          NotAllowedError, which is the autoplay policy.

import { FakeNode } from './stub_dom.mjs';

export const audioStub = {
  mode: 'full',
  contexts: [], // every FakeAudioContext handed out, in order
  decodeFailure: null, // a DOMException name `decodeAudioData` rejects with
};

// A labelled graph node. `connect` is recorded on the node doing the
// connecting, so a harness sees both halves of a graph edge (`osc#1` into
// `gain#2`). Nodes share it because Web Audio's `connect` is on
// `AudioNode`, which every one of them is.
class LabelledNode {
  constructor(kind, n, calls) {
    this.label = `${kind}#${n}`;
    this._calls = calls || [];
    this._kind = kind.split('#')[0];
  }
  connect(dst) {
    this._calls.push([`${this._kind}.connect`, this.label, dst.label]);
    return dst;
  }
}

// AudioParam automation. Records the calls the runtime makes, which is how
// a harness sees the envelope (attack peak, sustain, release to zero).
class FakeParam {
  constructor(calls, name) {
    this._calls = calls;
    this._name = name;
    // A plain assignment (`params.gain.value = 0.25`, which is how
    // `audio_set_master` sets the master) is recorded too, so a harness sees
    // a volume change without the automation API being involved.
    this._value = 0;
    Object.defineProperty(this, 'value', {
      configurable: true,
      get: () => this._value,
      set: (v) => {
        this._value = v;
        this._calls.push([`${this._name}.value=`, v]);
      },
    });
  }
  setValueAtTime(v, t) {
    this.value = v;
    this._calls.push([`${this._name}.setValueAtTime`, v, t]);
  }
  linearRampToValueAtTime(v, t) {
    this.value = v;
    this._calls.push([`${this._name}.linearRampToValueAtTime`, v, t]);
  }
}

class FakeGain extends LabelledNode {
  constructor(calls, n) {
    super('gain', n, calls);
    this.gain = new FakeParam(calls, `${this.label}.gain`);
  }
}

export class FakeAudioBuffer {
  constructor(channels, length, sampleRate) {
    this.numberOfChannels = channels;
    this.length = length;
    this.sampleRate = sampleRate;
    this.duration = length / sampleRate;
    this._data = new Float32Array(length);
  }
  getChannelData() { return this._data; }
  copyToChannel(src) { this._data.set(src.subarray(0, this._data.length)); }
}

export class FakeAudioContext {
  constructor() {
    this.state = 'suspended'; // the browser's initial state, and the point
    this.currentTime = 0;
    this.sampleRate = 48000;
    this.destination = new LabelledNode('destination', 0, this.calls);
    this.calls = [];
    this.counts = {};
    this.oscillators = [];
    this.sources = [];
    audioStub.contexts.push(this);
  }

  _new(kind) {
    this.counts[kind] = (this.counts[kind] || 0) + 1;
    return new LabelledNode(kind, this.counts[kind], this.calls);
  }

  resume() { this.state = 'running'; return Promise.resolve(); }
  suspend() { this.state = 'suspended'; return Promise.resolve(); }
  close() { this.state = 'closed'; return Promise.resolve(); }

  createGain() { return new FakeGain(this.calls, this._new('gain').label.split('#')[1]); }

  createOscillator() {
    const osc = this._new('osc');
    osc.type = 'sine';
    osc.frequency = new FakeParam(this.calls, `${osc.label}.frequency`);
    osc.started = false;
    osc.stopped = false;
    osc.start = (t) => {
      osc.started = true;
      this.calls.push(['osc.start', osc.label, t ?? 0]);
    };
    osc.stop = (t) => {
      // The runtime cuts a voice with `stop(0)`; an already-stopped
      // oscillator throws in a real browser, which is why `audio_stop`
      // swallows it. Record the call either way.
      if (osc.stopped) throw new Error('already stopped');
      osc.stopped = true;
      this.calls.push(['osc.stop', osc.label, t]);
    };
    this.oscillators.push(osc);
    return osc;
  }

  createBiquadFilter() {
    const f = this._new('filter');
    f.type = 'lowpass';
    f.frequency = new FakeParam(this.calls, `${f.label}.frequency`);
    return f;
  }

  createBufferSource() {
    const src = this._new('source');
    src.buffer = null;
    src.started = false;
    src.stopped = false;
    src.start = (when, offset, dur) => {
      src.started = true;
      this.calls.push(['source.start', src.label, when ?? 0, offset ?? 0, dur ?? 0]);
    };
    src.stop = (t) => {
      if (src.stopped) throw new Error('already stopped');
      src.stopped = true;
      this.calls.push(['source.stop', src.label, t]);
    };
    this.sources.push(src);
    return src;
  }

  createBuffer(channels, length, sampleRate) {
    return new FakeAudioBuffer(channels, length, sampleRate);
  }

  // A deterministic stand-in: the "decoded" buffer's sample count IS the
  // payload's byte count at 8 kHz, so a harness can prove the body arrived
  // whole (a truncated body would be a shorter buffer).
  decodeAudioData(arrayBuffer) {
    if (audioStub.decodeFailure) {
      return Promise.reject({ name: audioStub.decodeFailure });
    }
    const bytes = new Uint8Array(arrayBuffer);
    return Promise.resolve(new FakeAudioBuffer(1, Math.max(1, bytes.length), 8000));
  }
}

// ── HTMLMediaElement stub ─────────────────────────────────────────────

// Every instrumented media element, in creation order.
export const mediaStub = {
  elements: [],
};

function installMediaElement(node) {
  const rec = {
    node,
    paused: true,
    ended: false,
    seeking: false,
    muted: false,
    loop: false,
    readyState: 4, // HAVE_ENOUGH_DATA
    currentTime: 0,
    duration: 120, // two minutes
    volume: 1,
    playbackRate: 1,
    playCalls: 0,
    pauseCalls: 0,
  };
  const accessors = {
    paused: () => rec.paused,
    ended: () => rec.ended,
    seeking: () => rec.seeking,
    muted: [() => rec.muted, (v) => { rec.muted = !!v; }],
    loop: [() => rec.loop, (v) => { rec.loop = !!v; }],
    readyState: () => rec.readyState,
    currentTime: [() => rec.currentTime, (v) => { rec.currentTime = Number(v); }],
    duration: () => rec.duration,
    volume: [() => rec.volume, (v) => { rec.volume = Number(v); }],
    playbackRate: [() => rec.playbackRate, (v) => { rec.playbackRate = Number(v); }],
  };
  for (const [name, spec] of Object.entries(accessors)) {
    const [get, set] = Array.isArray(spec) ? spec : [spec, undefined];
    Object.defineProperty(node, name, { configurable: true, get, set });
  }
  node.play = () => {
    rec.playCalls += 1;
    if (audioStub.mode === 'blocked-play') {
      return Promise.reject({ name: 'NotAllowedError' });
    }
    rec.paused = false;
    rec.ended = false;
    return Promise.resolve();
  };
  node.pause = () => {
    rec.pauseCalls += 1;
    rec.paused = true;
  };
  mediaStub.elements.push(rec);
  return rec;
}

/// Put every instrumented element at its end, as a track finishing would.
export function finishMedia() {
  for (const rec of mediaStub.elements) {
    rec.paused = true;
    rec.ended = true;
    rec.currentTime = rec.duration;
  }
}

/// Install `AudioContext`/`AudioBuffer` and instrument media elements. Call
/// after `installDocument()`.
///
/// `document.createElement` is wrapped BEFORE the first element exists, so a
/// view's `<audio>` is instrumented as the patch creates it; anything
/// already mounted is walked too.
export function installAudio() {
  if (audioStub.mode === 'none') {
    delete globalThis.AudioContext;
    delete globalThis.webkitAudioContext;
  } else {
    globalThis.AudioContext = FakeAudioContext;
  }
  globalThis.AudioBuffer = FakeAudioBuffer;

  const instrument = (n) => {
    if (n.__oakMedia) return n;
    const tag = (n.tagName || '').toLowerCase();
    if (tag === 'audio' || tag === 'video') n.__oakMedia = installMediaElement(n);
    return n;
  };

  const doc = globalThis.document;
  const create = doc.createElement.bind(doc);
  doc.createElement = (tag) => instrument(create(tag));

  const walk = (n) => {
    instrument(n);
    for (const c of n.childNodes || []) walk(c);
  };
  if (doc.body) walk(doc.body);
}

export { FakeNode };
