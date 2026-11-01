// mty / spawn -- forkpty plus an FdStream over the master.
//
// Two invariants the FFI shape depends on:
//
//   * Environment is set parent-side before the fork and restored immediately
//     after. The child inherits it; `setenv` is never called in the child
//     (it is not async-signal-safe).
//   * Every ByteBuf is built before the fork, and `fork_exec`/`exec_die`
//     (and their `_cwd` variants) allocate nothing, so the child (a copy of a
//     Boehm-managed process) never allocates between `forkpty` and
//     `execl`/`_exit`.
//
// `SpawnConfig.cwd` is applied by a `chdir` in the child (async-signal-safe,
// no allocation): weaver reads a cwd-relative `./.weaver/config.toml`, and a
// test must not inherit the checkout's. A relative `bin` must be absolutized
// by the caller, because the exec happens after that `chdir`.

use lib::sys {
    forkpty, execl8, exit_now, chdir, setenv, unsetenv, ioctl, kill, waitpid,
    access, zero_i64, zero_i32, one_i32, code_127, sig_kill, sig_winch,
    tiocswinsz, x_ok
}
use std::bytebuf {
    ByteBuf, ByteBuf.alloc, ByteBuf.of_string, ByteBuf.of_list, ByteBuf.ptr,
    ByteBuf.length, ByteBuf.copy_into, ByteBuf.to_string, ByteBuf.free
}
use lib::ansi {Ansi.strip, Ansi.tight}
use lib::grid {Grid}
use std::io {IO.get_env, IO.current_time_nano}
use std::list {List.length}
use std::ref {Ref}
use std::stream {Stream, FdStream, FdStream.of_raw_fd, FdStream.poll, FdStream.poll_read}

/// Spawn parameters. `env` entries with `Option.none` unset the variable; the
/// parent's previous values are restored immediately after the fork, so one
/// test cannot leak into the next. `cwd` is the child's working directory
/// (none keeps the parent's); spell it at every literal -- an omitted field
/// has been seen to fill garbage in compiled code.
pub struct SpawnConfig {
    bin : String,
    args : List String,
    rows : I64,
    cols : I64,
    env : List (Pair String (Option String)),
    cwd : Option String
}

/// Everything the child has written, the screen model built from it, and how
/// many bytes of `raw` the grid has consumed. A trailing incomplete UTF-8
/// glyph or escape sequence leaves `parsed` behind; the next chunk retries it.
pub struct Output {
    raw : String,
    grid : Grid,
    parsed : I64,
    eof : Bool
}

pub def Output.empty (rows : I64) (cols : I64) : Output :=
    let o : Output := { raw := "", grid := Grid.empty rows cols, parsed := 0, eof := false } in
    o

pub def Output.push (o : Output) (chunk : String) : Output :=
    let raw2 := String.concat o.raw chunk in
    match Grid.feed_from o.grid raw2 o.parsed {
        Pair.pair g2 used =>
            let out : Output := { raw := raw2, grid := g2, parsed := used, eof := o.eof } in
            out
    }

/// The raw output with CSI/OSC removed and ASCII whitespace dropped -- the
/// Python drivers' `striptight`.
pub def Output.tight (o : Output) : String := Ansi.tight o.raw

/// The raw output with CSI/OSC removed but whitespace kept -- the Python
/// drivers' `strip`.
pub def Output.stripped (o : Output) : String := Ansi.strip o.raw

/// The raw bytes after `mark` (a byte offset into `raw`).
pub def Output.since (o : Output) (mark : I64) : String :=
    String.slice o.raw mark (String.length o.raw - mark)

/// A raw byte-substring probe (SGR codes, OSC 52 payloads).
pub def Output.contains (o : Output) (needle : String) : Bool := String.contains o.raw needle

/// The rendered screen position of `needle`, as terminal cell coordinates.
pub def Output.find (o : Output) (needle : String) : Option (Pair I64 I64) := Grid.find o.grid needle

pub def Output.row_text (o : Output) (r : I64) : String := Grid.row_text o.grid r

pub def Output.text (o : Output) : String := Grid.text o.grid

/// A child running on a pty master. The value is affine like `Child`; the
/// tests reuse it across calls under this mote's `[affine] warn`. `raw` is the
/// master descriptor, kept beside the stream for `ioctl` (the stream itself
/// has no fd-parameterized size call). `out` is the pump's accumulated state.
pub struct Mty {
    fd : FdStream,
    raw : I32,
    pid : I32,
    out : Ref Output
}

// ── NUL-terminated buffers ───────────────────────────────────────────────

/// A `ByteBuf` holding `s` plus one zero byte. `ByteBuf.of_string` does not
/// terminate, and `ByteBuf.alloc` zero-fills exactly its length, so allocate
/// `len + 1` and copy the source in.
def cstring_buf (s : String) : IO ByteBuf := do {
    let src <- ByteBuf.of_string s;
    let n := ByteBuf.length src;
    let dst <- ByteBuf.alloc (n + 1);
    let _ <- ByteBuf.copy_into dst 0 src;
    let _ <- ByteBuf.free src;
    return dst
}

/// `struct winsize` bytes: rows lo, rows hi, cols lo, cols hi, four zero
/// padding bytes. Built in a top-level def (a list literal inside a do-block
/// is a known lowering trap).
def lo_byte (n : I64) : U8 := U32.to_u8 (U32.and (I64.to_u32 n) (I64.to_u32 255))

def hi_byte (n : I64) : U8 := U32.to_u8 (U32.shr (I64.to_u32 n) (I64.to_u32 8))

def winsize_bytes (rows : I64) (cols : I64) : List U8 :=
    [lo_byte rows, hi_byte rows, lo_byte cols, hi_byte cols, 0u8, 0u8, 0u8, 0u8]

/// The eight fixed argv slots, so the caller can destructure fields (the
/// parser has no nested patterns) without allocating after the last buffer.
struct ArgBufs {
    b0 : ByteBuf,
    b1 : ByteBuf,
    b2 : ByteBuf,
    b3 : ByteBuf,
    b4 : ByteBuf,
    b5 : ByteBuf,
    b6 : ByteBuf,
    b7 : ByteBuf
}

def build_argv_bufs (w0 : String) (w1 : String) (w2 : String) (w3 : String) (w4 : String) (w5 : String) (w6 : String) (w7 : String) : IO ArgBufs := do {
    let b0 <- cstring_buf w0;
    let b1 <- cstring_buf w1;
    let b2 <- cstring_buf w2;
    let b3 <- cstring_buf w3;
    let b4 <- cstring_buf w4;
    let b5 <- cstring_buf w5;
    let b6 <- cstring_buf w6;
    let b7 <- cstring_buf w7;
    let out : ArgBufs := {
        b0 := b0, b1 := b1, b2 := b2, b3 := b3,
        b4 := b4, b5 := b5, b6 := b6, b7 := b7
    };
    return out
}

/// The `index`-th word, or "" past the end. The caller only marks the first
/// `used` slots as real, so a filler is never passed as an argument.
def word_at (ws : List String) (index : I64) : String :=
    match List.get index ws {
        Option.some s => s,
        Option.none => ""
    }

/// Slot `i`'s pointer, or a real NULL terminator for an absent slot.
def slot_ptr (b : ByteBuf) (i : I64) (used : I64) : Ptr :=
    if I64.lt i used then ByteBuf.ptr b else Ptr.null

// ── The allocation-free fork/exec child path ─────────────────────────────

def fork_exec (amaster : Ptr) (win : Ptr) (path : Ptr)
               (a0 : Ptr) (a1 : Ptr) (a2 : Ptr) (a3 : Ptr)
               (a4 : Ptr) (a5 : Ptr) (a6 : Ptr) (a7 : Ptr) : I32 :=
    let pid : I32 := forkpty amaster Ptr.null Ptr.null win in
    if I64.beq (I32.to_i64 pid) zero_i64
    then exec_die path a0 a1 a2 a3 a4 a5 a6 a7
    else pid

def exec_die (path : Ptr) (a0 : Ptr) (a1 : Ptr) (a2 : Ptr) (a3 : Ptr)
              (a4 : Ptr) (a5 : Ptr) (a6 : Ptr) (a7 : Ptr) : I32 :=
    let _rc : I32 := execl8 path a0 a1 a2 a3 a4 a5 a6 a7 in
    exit_now code_127

/// `fork_exec` with a child-side `chdir` first. Both branches stay pure and
/// allocation-free; branching on `chdir`'s result keeps the extern
/// observable (an unused pure call could be eliminated).
def fork_exec_cwd (amaster : Ptr) (win : Ptr) (cwd : Ptr) (path : Ptr)
                  (a0 : Ptr) (a1 : Ptr) (a2 : Ptr) (a3 : Ptr)
                  (a4 : Ptr) (a5 : Ptr) (a6 : Ptr) (a7 : Ptr) : I32 :=
    let pid : I32 := forkpty amaster Ptr.null Ptr.null win in
    if I64.beq (I32.to_i64 pid) zero_i64
    then exec_die_cwd cwd path a0 a1 a2 a3 a4 a5 a6 a7
    else pid

def exec_die_cwd (cwd : Ptr) (path : Ptr) (a0 : Ptr) (a1 : Ptr) (a2 : Ptr) (a3 : Ptr)
                 (a4 : Ptr) (a5 : Ptr) (a6 : Ptr) (a7 : Ptr) : I32 :=
    let rc : I32 := chdir cwd in
    if I64.beq (I32.to_i64 rc) zero_i64
    then exec_die path a0 a1 a2 a3 a4 a5 a6 a7
    else exit_now code_127

// ── Environment ──────────────────────────────────────────────────────────

def apply_value (k : String) (v : Option String) : IO Unit :=
    match v {
        Option.some value => do { let _ <- IO.mk (setenv k value one_i32); return unit },
        Option.none => do { let _ <- IO.mk (unsetenv k); return unit }
    }

def apply_entry (e : Pair String (Option String)) : IO Unit :=
    match e { Pair.pair k v => apply_value k v }

def apply_env (env : List (Pair String (Option String))) : IO Unit :=
    match env {
        List.empty => IO.pure unit,
        List.cons e rest => do { let _ <- apply_entry e; apply_env rest }
    }

def save_entry (e : Pair String (Option String)) : IO (Pair String (Option String)) :=
    match e { Pair.pair k _v => do { let old <- IO.get_env k; return (Pair.pair k old) } }

def save_env (env : List (Pair String (Option String))) : IO (List (Pair String (Option String))) :=
    match env {
        List.empty => IO.pure List.empty,
        List.cons e rest => do {
            let old <- save_entry e;
            let tail <- save_env rest;
            return (List.cons old tail)
        }
    }

def restore_env (saved : List (Pair String (Option String))) : IO Unit :=
    match saved {
        List.empty => IO.pure unit,
        List.cons e rest => do { let _ <- apply_entry e; restore_env rest }
    }

// ── Spawn ─────────────────────────────────────────────────────────────────

def nth_u8 (xs : List U8) (i : I64) : I64 :=
    match List.get i xs {
        Option.some b => U8.to_i64 b,
        Option.none => 0
    }

/// Little-endian decode of the 4-byte `int` `forkpty` wrote into `amaster`.
def decode_fd (xs : List U8) : I64 :=
    nth_u8 xs 0 + 256 * (nth_u8 xs 1 + 256 * (nth_u8 xs 2 + 256 * nth_u8 xs 3))

/// The number of real argv slots: argv[0] plus at most seven arguments.
def used_slots (args_n : I64) : I64 :=
    if I64.lt args_n 7 then args_n + 1 else 8

pub def Mty.spawn (cfg : SpawnConfig) : IO (Result String Mty) := do {
    let args_n := List.length cfg.args;
    if I64.gt args_n 7 then do {
        return (Result.err "mty: too many argv words (max 7 arguments)")
    } else do {
        let found := access cfg.bin x_ok;
        if Bool.not (I64.beq (I32.to_i64 found) zero_i64) then do {
            return (Result.err (String.concat "mty: not executable: " cfg.bin))
        } else do {
            let ws : List String := List.cons cfg.bin cfg.args;
            let used := used_slots args_n;
            let cwd_s : String := match cfg.cwd {
                Option.some s => s,
                Option.none => ""
            };
            let use_cwd := Bool.not (String.is_empty cwd_s);
            let saved <- save_env cfg.env;
            let _ <- apply_env cfg.env;
            let cwd <- cstring_buf cwd_s;
            let bufs <- build_argv_bufs
                (word_at ws 0) (word_at ws 1) (word_at ws 2) (word_at ws 3)
                (word_at ws 4) (word_at ws 5) (word_at ws 6) (word_at ws 7);
            let amaster <- ByteBuf.alloc 8;
            let win <- ByteBuf.of_list (winsize_bytes cfg.rows cfg.cols);
            let p0 := slot_ptr bufs.b0 0 used;
            let p1 := slot_ptr bufs.b1 1 used;
            let p2 := slot_ptr bufs.b2 2 used;
            let p3 := slot_ptr bufs.b3 3 used;
            let p4 := slot_ptr bufs.b4 4 used;
            let p5 := slot_ptr bufs.b5 5 used;
            let p6 := slot_ptr bufs.b6 6 used;
            let p7 := slot_ptr bufs.b7 7 used;
            let path := ByteBuf.ptr bufs.b0;
            let pid : I32 := if use_cwd
                then fork_exec_cwd (ByteBuf.ptr amaster) (ByteBuf.ptr win) (ByteBuf.ptr cwd)
                    path p0 p1 p2 p3 p4 p5 p6 p7
                else fork_exec (ByteBuf.ptr amaster) (ByteBuf.ptr win)
                    path p0 p1 p2 p3 p4 p5 p6 p7;
            let _ <- restore_env saved;
            let out <- Ref.new (Output.empty cfg.rows cfg.cols);
            Mty.spawn_done amaster win cwd bufs pid out
        }
    }
}

/// The parent half after the fork: decode the master fd, release the pre-fork
/// buffers, and hand back the handle. The child never reaches this (it is
/// inside `fork_exec`'s `exec_die`).
def Mty.spawn_done (amaster : ByteBuf) (win : ByteBuf) (cwd : ByteBuf) (bufs : ArgBufs) (pid : I32) (out : Ref Output) : IO (Result String Mty) := do {
    let fds <- ByteBuf.to_list amaster 4;
    let fd := I64.to_i32 (decode_fd fds);
    let _ <- ByteBuf.free amaster;
    let _ <- ByteBuf.free win;
    let _ <- ByteBuf.free cwd;
    let _ <- ByteBuf.free bufs.b0;
    let _ <- ByteBuf.free bufs.b1;
    let _ <- ByteBuf.free bufs.b2;
    let _ <- ByteBuf.free bufs.b3;
    let _ <- ByteBuf.free bufs.b4;
    let _ <- ByteBuf.free bufs.b5;
    let _ <- ByteBuf.free bufs.b6;
    let _ <- ByteBuf.free bufs.b7;
    if I64.lt (I32.to_i64 pid) zero_i64 then do {
        return (Result.err "mty: forkpty failed")
    } else do {
        let m : Mty := { fd := FdStream.of_raw_fd fd, raw := fd, pid := pid, out := out };
        return (Result.ok m)
    }
}

// ── I/O ───────────────────────────────────────────────────────────────────

/// Write all of `s` to the child. Errors (EPIPE after an exit) are ignored:
/// the caller's next pump observes EOF.
pub def Mty.send_text (m : Mty) (s : String) : IO Unit := do {
    let view : FdStream := m.fd;
    let buf <- ByteBuf.of_string s;
    let _ <- Stream.write view buf;
    let _ <- ByteBuf.free buf;
    return unit
}

/// Write `s` in byte-sized chunks with a pump between them. A single large
/// write can block against a dialog reading one byte per syscall; pastes are
/// ASCII, so a byte offset is always a character boundary. `chunk_bytes` is
/// clamped to at least 1.
pub def Mty.send_chunked (m : Mty) (s : String) (chunk_bytes : I64) (pause_ms : I64) : IO Unit := do {
    let step := if I64.lt chunk_bytes 1 then 1 else chunk_bytes;
    send_chunked_go m s (String.length s) step pause_ms 0
}

#[partial]
def send_chunked_go (m : Mty) (s : String) (total : I64) (chunk : I64) (pause : I64) (off : I64) : IO Unit := do {
    if Bool.not (I64.lt off total) then IO.pure unit
    else do {
        let rest := total - off;
        let n := if I64.lt chunk rest then chunk else rest;
        Mty.send_text m (String.slice s off n);
        Mty.pump m pause;
        send_chunked_go m s total chunk pause (off + n)
    }
}

/// Set the master's `TIOCSWINSZ` and send SIGWINCH. Weaver observes size by
/// polling `TIOCGWINSZ`, so the ioctl is the mechanism; the signal matches the
/// Python oracle and wakes a poll blocked on input. Errors are ignored (the
/// child may already be gone).
pub def Mty.resize (m : Mty) (rows : I64) (cols : I64) : IO Unit := do {
    let win <- ByteBuf.of_list (winsize_bytes rows cols);
    let _ <- IO.mk (ioctl m.raw tiocswinsz (ByteBuf.ptr win));
    let _ <- ByteBuf.free win;
    // The old geometry cannot be mapped onto the new one; weaver clears and
    // repaints, so the grid model restarts blank and the clear counts.
    let _ <- Ref.update m.out (fn (o : Output) => { o with grid := Grid.empty rows cols });
    let _ <- IO.mk (kill m.pid sig_winch);
    return unit
}

// ── Pump and event-driven waits ───────────────────────────────────────────

/// The current accumulated output and screen model.
pub def Mty.output (m : Mty) : IO Output := Ref.get m.out

/// Pump readable output for up to `ms`, in 100 ms poll slices.
pub def Mty.pump (m : Mty) (ms : I64) : IO Unit := do {
    let now <- IO.current_time_nano;
    pump_until m (now + ms * 1000000)
}

#[partial]
def pump_until (m : Mty) (deadline : I64) : IO Unit := do {
    let o <- Ref.get m.out;
    if o.eof then IO.pure unit
    else do {
        let now <- IO.current_time_nano;
        if I64.gt now deadline then IO.pure unit
        else do {
            let ready <- FdStream.poll m.fd FdStream.poll_read 100;
            match ready {
                Result.err _ => mark_eof m,
                Result.ok r =>
                    if Bool.not r then pump_until m deadline else pump_read m deadline
            }
        }
    }
}

#[partial]
def pump_read (m : Mty) (deadline : I64) : IO Unit := do {
    let r <- Stream.read m.fd 65536;
    match r {
        Result.err _ => mark_eof m,
        Result.ok buf => do {
            let n := ByteBuf.length buf;
            if I64.lt n 1 then do {
                let _ <- ByteBuf.free buf;
                mark_eof m
            } else do {
                let s <- ByteBuf.to_string buf n;
                let _ <- ByteBuf.free buf;
                let _ <- Ref.update m.out (fn (o : Output) => Output.push o s);
                pump_until m deadline
            }
        }
    }
}

def mark_eof (m : Mty) : IO Unit := do {
    let _ <- Ref.update m.out (fn (o : Output) => { o with eof := true });
    return unit
}

/// Pump until `pred` sees what it wants, or the deadline expires. This is the
/// replacement for every fixed `time.sleep` in the Python drivers.
pub def Mty.wait_until (m : Mty) (pred : Output -> Bool) (deadline_ms : I64) : IO Bool := do {
    let start <- IO.current_time_nano;
    wait_until_go m pred (start + deadline_ms * 1000000)
}

#[partial]
def wait_until_go (m : Mty) (pred : Output -> Bool) (deadline : I64) : IO Bool := do {
    let o <- Ref.get m.out;
    let eof := o.eof;
    if pred o then IO.pure true
    else if eof then IO.pure false
    else do {
        let now <- IO.current_time_nano;
        if I64.gt now deadline then IO.pure false
        else do {
            Mty.pump m 100;
            wait_until_go m pred deadline
        }
    }
}

/// Pump until no bytes have arrived for `idle_ms` (true), EOF (true), or the
/// overall deadline expires (false). The replacement for a fixed post-send
/// sleep.
pub def Mty.wait_quiet (m : Mty) (idle_ms : I64) (deadline_ms : I64) : IO Bool := do {
    let start <- IO.current_time_nano;
    quiet_go m idle_ms (start + idle_ms * 1000000) (start + deadline_ms * 1000000)
}

#[partial]
def quiet_go (m : Mty) (idle_ms : I64) (idle_at : I64) (deadline : I64) : IO Bool := do {
    let o <- Ref.get m.out;
    let eof := o.eof;
    let before := String.length o.raw;
    if eof then IO.pure true
    else do {
        Mty.pump m 100;
        let o2 <- Ref.get m.out;
        let eof2 := o2.eof;
        let after := String.length o2.raw;
        let now <- IO.current_time_nano;
        let idle_at2 := if I64.gt after before then now + idle_ms * 1000000 else idle_at;
        let quiet := Bool.and (I64.beq after before) (Bool.not (I64.lt now idle_at));
        if eof2 then IO.pure true
        else if quiet then IO.pure true
        else if I64.gt now deadline then IO.pure false
        else quiet_go m idle_ms idle_at2 deadline
    }
}

/// Everything the child writes until EOF or `deadline_ms` from now, joined
/// into one String. Phase 0 only: Phase 1 replaces this with the incremental
/// Output/grid state and `wait_until`.
pub def Mty.read_all (m : Mty) (deadline_ms : I64) : IO String := do {    let start <- IO.current_time_nano;
    let deadline := start + deadline_ms * 1000000;
    let view : FdStream := m.fd;
    read_loop view deadline List.empty
}

#[partial]
def read_loop (fd : FdStream) (deadline : I64) (acc : List String) : IO String := do {
    let now <- IO.current_time_nano;
    if I64.gt now deadline then IO.pure (String.concat_list (List.reverse acc))
    else do {
        let ready <- FdStream.poll fd FdStream.poll_read 100;
        match ready {
            Result.err _ => IO.pure (String.concat_list (List.reverse acc)),
            Result.ok r =>
                if Bool.not r
                then read_loop fd deadline acc
                else read_once fd deadline acc
        }
    }
}

#[partial]
def read_once (fd : FdStream) (deadline : I64) (acc : List String) : IO String := do {
    let r <- Stream.read fd 65536;
    match r {
        Result.err _ => IO.pure (String.concat_list (List.reverse acc)),
        Result.ok buf => do {
            let n := ByteBuf.length buf;
            if I64.lt n 1 then do {
                let _ <- ByteBuf.free buf;
                return (String.concat_list (List.reverse acc))
            } else do {
                let s <- ByteBuf.to_string buf n;
                let _ <- ByteBuf.free buf;
                read_loop fd deadline (List.cons s acc)
            }
        }
    }
}

/// Reap the child; returns the pid `waitpid` reported, or -1 on error.
pub def Mty.reap (m : Mty) : IO I64 := do {
    let p <- IO.mk (waitpid m.pid Ptr.null zero_i32);
    return (I32.to_i64 p)
}

/// The child's pid, for `/proc/<pid>` probes (RSS).
pub def Mty.child_pid (m : Mty) : I64 := I32.to_i64 m.pid

/// `kill(pid, 0) == 0`: still alive (or a zombie awaiting reaping).
pub def Mty.pid_alive (pid : I64) : IO Bool := do {
    let rc <- IO.mk (kill (I64.to_i32 pid) zero_i32);
    return (I64.beq (I32.to_i64 rc) zero_i64)
}

/// `kill(pid, 0) == 0` for this child.
pub def Mty.alive (m : Mty) : IO Bool := Mty.pid_alive (Mty.child_pid m)

pub def Mty.terminate (m : Mty) : IO Unit := do {
    let _ <- IO.mk (kill m.pid sig_kill);
    return unit
}

pub def Mty.close (m : Mty) : IO Unit := do {
    let view : FdStream := m.fd;
    Stream.close view
}

/// Phase 0 teardown: two Ctrl+C bytes, a short drain, SIGKILL if still
/// alive, reap, close. The Phase 1 `finish` reports whether `?1049l` was seen.
pub def Mty.finish (m : Mty) : IO Unit := do {
    Mty.send_text m "\u{3}";
    Mty.send_text m "\u{3}";
    Mty.pump m 500;
    let here <- Mty.alive m;
    let _ <- (match here { true => Mty.terminate m, false => IO.pure unit });
    let _ <- Mty.reap m;
    Mty.close m
}
