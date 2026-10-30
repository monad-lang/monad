/// Transformer server: deadlines, `Expect: 100-continue`, chunked request
/// bodies, strict Host parsing, and continuous acceptance.

use std::concurrent::combine {sleepIO}
use std::concurrent::fiber {FiberError}
use std::list {List.length}
use std::stream {Stream, FdStream}
use std::test {}
use http::body {Body.to_bytes_pure}
use http::types {
  Body, Response, Response.ok_text, Transport, Transport.read_bytes,
  Transport.write_bytes,
}
use moon::handler_t {
  HandlerT, HandlerT.body_bytes_io, HandlerT.pure_io, HttpError,
}
use moon::server {
  ServerConfig, ServerConfig.on, ServerConfig.with_timeouts,
  ServerHandleT, Server.start_t, Server.shutdown_t, Server.wait_t,
}

def hello_handler : HandlerT IO Response :=
  HandlerT.pure_io (Response.ok_text "hello")

def echo_len_handler : HandlerT IO Response := do {
  let bytes : List U8 <- HandlerT.body_bytes_io;
  HandlerT.pure_io (Response.ok_text (I64.to_string (List.length bytes)))
}

def write_text (sock : FdStream) (s : String) : IO Bool := do {
  let t : Transport := Transport.plain sock;
  let r <- Transport.write_bytes t (String.to_list s);
  match r {
    Result.err _ => IO.pure false,
    Result.ok _ => IO.pure true
  }
}

#[terminating]
def read_all_more (sock : FdStream) (bytes : List U8) : IO (Result String String) := do {
  let rest <- read_all sock;
  match rest {
    Result.ok s => IO.pure (Result.ok (String.concat (String.from_list bytes) s)),
    Result.err e => IO.pure (Result.err e)
  }
}

#[terminating]
def read_all (sock : FdStream) : IO (Result String String) := do {
  let t : Transport := Transport.plain sock;
  let r <- Transport.read_bytes t 4096i64;
  match r {
    Result.err e => IO.pure (Result.err e),
    Result.ok bytes =>
      if List.is_empty bytes
      then IO.pure (Result.ok "")
      else read_all_more sock bytes
  }
}

#[terminating]
def read_until_more (sock : FdStream) (suffix : String) (acc : String)
    (bytes : List U8) : IO (Result String String) :=
  read_until sock suffix (String.concat acc (String.from_list bytes))

#[terminating]
def read_until (sock : FdStream) (suffix : String) (acc : String) :
    IO (Result String String) := do {
  if String.contains acc suffix
  then IO.pure (Result.ok acc)
  else do {
    let t : Transport := Transport.plain sock;
    let r <- Transport.read_bytes t 4096i64;
    match r {
      Result.err e => IO.pure (Result.err e),
      Result.ok bytes =>
        if List.is_empty bytes
        then IO.pure (Result.err "connection closed before suffix")
        else read_until_more sock suffix acc bytes
    }
  }
}

def with_client (port : U16) (body : FdStream -> IO Bool) : IO Bool := do {
  let c <- IO.tcp_connect "127.0.0.1" port;
  match c {
    Result.err _ => IO.pure false,
    Result.ok sock => do {
      let r <- body sock;
      Stream.close sock;
      IO.pure r
    }
  }
}

def start_on_zero (cfg : ServerConfig) (handler : HandlerT IO Response) :
    IO (Result String (Pair ServerHandleT U16)) := do {
  let started <- Server.start_t cfg handler;
  match started {
    Result.err e => IO.pure (Result.err e),
    Result.ok h => do {
      let port <- IO.tcp_local_port h.listener;
      IO.pure (Result.ok (Pair.pair h port))
    }
  }
}

def stop (h : ServerHandleT) : IO Unit := do {
  Server.shutdown_t h;
  let _w : Result FiberError Unit <- Server.wait_t h;
  return unit
}

#[test]
def test_rt_get : IO Bool := do {
  let started <- start_on_zero (ServerConfig.on 0u16) hello_handler;
  match started {
    Result.err _ => IO.pure false,
    Result.ok pr =>
      match pr {
        Pair.pair h port => do {
          let ok <- with_client port (fn (sock : FdStream) => do {
            let _w : Bool <- write_text sock
              "GET / HTTP/1.1\r\nHost: x\r\nConnection: close\r\n\r\n";
            let resp : Result String String <- read_all sock;
            match resp {
              Result.ok s => IO.pure (Bool.and (String.contains s "200") (String.contains s "hello")),
              Result.err _ => IO.pure false
            }
          });
          stop h;
          IO.pure ok
        }
      }
  }
}

#[test]
def test_rt_missing_host_rejected : IO Bool := do {
  let started <- start_on_zero (ServerConfig.on 0u16) hello_handler;
  match started {
    Result.err _ => IO.pure false,
    Result.ok pr =>
      match pr {
        Pair.pair h port => do {
          let ok <- with_client port (fn (sock : FdStream) => do {
            let _w : Bool <- write_text sock
              "GET / HTTP/1.1\r\nConnection: close\r\n\r\n";
            let resp : Result String String <- read_all sock;
            match resp {
              Result.ok s => IO.pure (String.contains s "400"),
              Result.err _ => IO.pure false
            }
          });
          stop h;
          IO.pure ok
        }
      }
  }
}

#[test]
def test_rt_whitespace_header_rejected : IO Bool := do {
  let started <- start_on_zero (ServerConfig.on 0u16) hello_handler;
  match started {
    Result.err _ => IO.pure false,
    Result.ok pr =>
      match pr {
        Pair.pair h port => do {
          let ok <- with_client port (fn (sock : FdStream) => do {
            let _w : Bool <- write_text sock
              "POST / HTTP/1.1\r\nHost: x\r\nContent-Length : 5\r\nConnection: close\r\n\r\nhello";
            let resp : Result String String <- read_all sock;
            match resp {
              Result.ok s => IO.pure (String.contains s "400"),
              Result.err _ => IO.pure false
            }
          });
          stop h;
          IO.pure ok
        }
      }
  }
}

#[test]
def test_rt_expect_continue : IO Bool := do {
  let started <- start_on_zero (ServerConfig.on 0u16) echo_len_handler;
  match started {
    Result.err _ => IO.pure false,
    Result.ok pr =>
      match pr {
        Pair.pair h port => do {
          let ok <- with_client port (fn (sock : FdStream) => do {
            let _w : Bool <- write_text sock
              "POST / HTTP/1.1\r\nHost: x\r\nContent-Length: 5\r\nExpect: 100-continue\r\nConnection: close\r\n\r\n";
            let interim : Result String String <- read_until sock "\r\n\r\n" "";
            match interim {
              Result.err _ => IO.pure false,
              Result.ok first =>
                if Bool.not (String.contains first "100")
                then IO.pure false
                else do {
                  let _w2 : Bool <- write_text sock "hello";
                  let final : Result String String <- read_all sock;
                  match final {
                    Result.ok s =>
                      IO.pure (Bool.and (String.contains s "200") (String.contains s "5")),
                    Result.err _ => IO.pure false
                  }
                }
            }
          });
          stop h;
          IO.pure ok
        }
      }
  }
}

#[test]
def test_rt_chunked_request : IO Bool := do {
  let started <- start_on_zero (ServerConfig.on 0u16) echo_len_handler;
  match started {
    Result.err _ => IO.pure false,
    Result.ok pr =>
      match pr {
        Pair.pair h port => do {
          let ok <- with_client port (fn (sock : FdStream) => do {
            let _w : Bool <- write_text sock
              "POST / HTTP/1.1\r\nHost: x\r\nTransfer-Encoding: chunked\r\nConnection: close\r\n\r\n5\r\nhello\r\n0\r\n\r\n";
            let resp : Result String String <- read_all sock;
            match resp {
              Result.ok s => IO.pure (Bool.and (String.contains s "200") (String.contains s "5")),
              Result.err _ => IO.pure false
            }
          });
          stop h;
          IO.pure ok
        }
      }
  }
}

#[test]
def test_rt_head_timeout : IO Bool := do {
  let cfg := ServerConfig.with_timeouts 200i64 1000i64 1000i64 1000i64
    (ServerConfig.on 0u16);
  let started <- start_on_zero cfg hello_handler;
  match started {
    Result.err _ => IO.pure false,
    Result.ok pr =>
      match pr {
        Pair.pair h port => do {
          let ok <- with_client port (fn (sock : FdStream) => do {
            let _w : Bool <- write_text sock "GET / HTTP/1.1\r\n";
            sleepIO 500i64;
            let resp : Result String String <- read_all sock;
            match resp {
              Result.ok s => IO.pure (String.contains s "408"),
              Result.err _ => IO.pure false
            }
          });
          stop h;
          IO.pure ok
        }
      }
  }
}

def idle_no_connect (h : ServerHandleT) : IO Bool := do {
  stop h;
  IO.pure false
}

def idle_second (h : ServerHandleT) (port : U16) (s1 : FdStream) : IO Bool := do {
  let ok <- with_client port (fn (sock : FdStream) => do {
    let _w2 : Bool <- write_text sock
      "GET / HTTP/1.1\r\nHost: x\r\nConnection: close\r\n\r\n";
    let resp : Result String String <- read_all sock;
    match resp {
      Result.ok s => IO.pure (String.contains s "200"),
      Result.err _ => IO.pure false
    }
  });
  Stream.close s1;
  stop h;
  IO.pure ok
}

def idle_first (h : ServerHandleT) (port : U16) (s1 : FdStream) : IO Bool := do {
  let _w1 : Bool <- write_text s1 "GET / HTTP/1.1\r\nHost: x\r\n\r\n";
  let head1 : Result String String <- read_until s1 "\r\n\r\n" "";
  let ok <- idle_second h port s1;
  match head1 {
    Result.ok _ => IO.pure ok,
    Result.err _ => IO.pure false
  }
}

#[test]
def test_rt_idle_connection_does_not_block : IO Bool := do {
  let started <- start_on_zero (ServerConfig.on 0u16) hello_handler;
  match started {
    Result.err _ => IO.pure false,
    Result.ok pr =>
      match pr {
        Pair.pair h port => do {
          let c1 <- IO.tcp_connect "127.0.0.1" port;
          match c1 {
            Result.err _ => idle_no_connect h,
            Result.ok s1 => idle_first h port s1
          }
        }
      }
  }
}
