// WebGL from an Oak program, end to end: the view renders a `<canvas>`, the
// animation-frame subscription drives `update`, and every frame's drawing is
// a `Command.after_render` effect, so it runs after the patch has put the
// canvas in the DOM.
//
// The first frame asks for `setup` (context, canvas fit, shader program);
// its result comes back as a message and the model keeps the handles. Later
// frames ask for `draw`. A deliberately broken shader checks that a compile
// error carries the driver's info log.
//
// `wasm/web/webgl_smoke.mjs` runs it over the stub DOM plus
// `wasm/web/stub_gl.mjs` and compares the recorded GL call stream.
#![mote { name := "oak_webgl", deps := [oak, oak_wasm, web_wasm, web_event] }]

use oak::typed {Oak.Node}
use oak::elements {Html.canvas, Html.div, Html.id_, Html.span, Html.text}
use web_event::event {WebEvent}
use oak::events {Subscription}
use oak::app {Command, Host, Program}
use oak_wasm::program {Runtime.dispatch, Runtime.mount, Runtime.tick}
use web_wasm::dom {Dom.query}
use web_wasm::canvas {Canvas.fit, Canvas.pixel_ratio}
use web_wasm::gl {
    GlContext, GlProgram, GlUniform, GlOptions, GlOptions.default, GlShaderStage, GlPrimitive,
    GlClear, GlCap, Gl.context, Gl.version, Gl.drawing_buffer_size, Gl.compile_shader,
    Gl.program, Gl.use_program, Gl.uniform_location, Gl.uniform1f, Gl.viewport,
    Gl.clear_color, Gl.clear, Gl.enable, Gl.draw_arrays, Gl.has_vertex_arrays,
}

/// What the model keeps once setup succeeds.
struct Scene {
    ctx : GlContext,
    program : GlProgram,
    time : GlUniform
}

instance Copy Scene {
    def copy (s : Scene) : Pair Scene Scene := Pair.pair s s
}

type Fx {
    setup,
    draw (scene : Scene) (t : F64)
}

type Msg {
    frame (t : F64),
    ready (scene : Scene) (report : String),
    failed (error : String),
    drew
}

struct Model {
    status : String,
    scene : Option Scene,
    frames : I64,
    setting_up : Bool
}

def init : Model := { status := "init", scene := Option.none, frames := 0, setting_up := false }

def vertex_source : String :=
    "attribute vec2 a_position; void main() { gl_Position = vec4(a_position, 0.0, 1.0); }"

def fragment_source : String :=
    "precision mediump float; uniform float u_time; void main() { gl_FragColor = vec4(u_time, 0.0, 0.0, 1.0); }"

def on_frame (status : String) (scene : Option Scene) (frames : I64) (setting_up : Bool) (t : F64)
    : Pair Model (Command Fx Msg) :=
    match scene {
        Option.some s =>
            let m : Model := { status := status, scene := Option.some s, frames := frames + 1,
                setting_up := false } in
            Pair.pair m (Command.after_render (Fx.draw s t)),
        Option.none =>
            if setting_up
            then
                let m : Model := { status := status, scene := Option.none, frames := frames,
                    setting_up := true } in
                Pair.pair m Command.none
            else
                let m : Model := { status := status, scene := Option.none, frames := frames,
                    setting_up := true } in
                Pair.pair m (Command.after_render Fx.setup),
    }

def update (model : Model) (msg : Msg) : Pair Model (Command Fx Msg) :=
    match model {
        { status, scene, frames, setting_up } =>
            match msg {
                Msg.frame t => on_frame status scene frames setting_up t,
                Msg.ready s report =>
                    let m : Model := { status := report, scene := Option.some s, frames := frames,
                        setting_up := false } in
                    Pair.pair m Command.none,
                Msg.failed e =>
                    let m : Model := { status := String.concat "failed: " e, scene := scene,
                        frames := frames, setting_up := false } in
                    Pair.pair m Command.none,
                Msg.drew =>
                    let m : Model := { status := status, scene := scene, frames := frames,
                        setting_up := setting_up } in
                    Pair.pair m Command.none,
            },
    }

def subs (_m : Model) : List (Subscription Msg) :=
    [Subscription.animation_frame (fn (e : WebEvent) => Msg.frame e.time_stamp)]

def frames_text (m : Model) : String :=
    match m { { status, frames, .. } => String.concat_list [status, " frames=", I64.to_string frames] }

def view (m : Model) : Oak.Node Msg :=
    Html.div [Html.id_ "app"]
        [Html.canvas [Html.id_ "board"] List.empty,
            Html.span [Html.id_ "status"] [Html.text (frames_text m)]]

def app : Program Model Msg Fx := Program.with_subs init update view subs

// ─── The host: the only place that touches WebGL ─────────────────────

def yes_no (b : Bool) : String := if b then "yes" else "no"

/// A shader that must NOT compile: its error has to carry the info log.
def bad_shader_report (ctx : GlContext) : IO String := do {
    let r <- Gl.compile_shader ctx GlShaderStage.fragment "#error broken";
    match r {
        Result.err log => return (String.concat "badlog=" log),
        Result.ok _ => return "badlog=MISSING",
    }
}

def finish_setup (ctx : GlContext) (program : GlProgram) (resized : Bool) (dpr : F64) : IO (Option Msg) := do {
    let version <- Gl.version ctx;
    let vaos <- Gl.has_vertex_arrays ctx;
    let bad <- bad_shader_report ctx;
    let loc <- Gl.uniform_location ctx program "u_time";
    match loc {
        Option.none => return (Option.some (Msg.failed "no u_time")),
        Option.some time => do {
            let scene : Scene := { ctx := ctx, program := program, time := time };
            let report : String := String.concat_list [
                "webgl", I64.to_string version, " fit=", yes_no resized,
                " dpr=", F64.to_string dpr, " vao=", yes_no vaos, " ", bad,
            ];
            return (Option.some (Msg.ready scene report))
        },
    }
}

def setup_with (ctx : GlContext) (resized : Bool) (dpr : F64) : IO (Option Msg) := do {
    let built <- Gl.program ctx vertex_source fragment_source;
    match built {
        Result.err e => return (Option.some (Msg.failed e)),
        Result.ok program => finish_setup ctx program resized dpr,
    }
}

def setup : IO (Option Msg) := do {
    let canvas <- Dom.query "#board";
    let resized <- Canvas.fit canvas;
    let dpr <- Canvas.pixel_ratio canvas;
    let found <- Gl.context canvas GlOptions.default;
    match found {
        Option.none => return (Option.some (Msg.failed "no webgl")),
        Option.some ctx => setup_with ctx resized dpr,
    }
}

def viewport_to (ctx : GlContext) (size : Pair I64 I64) : IO Unit :=
    match size { Pair.pair w h => Gl.viewport ctx 0 0 w h }

def draw (s : Scene) (t : F64) : IO (Option Msg) :=
    match s {
        { ctx, program, time } => do {
            let size <- Gl.drawing_buffer_size ctx;
            let _ <- viewport_to ctx size;
            let _ <- Gl.clear_color ctx 0.0 0.0 0.0 1.0;
            let mask : GlClear := { color := true, depth := true, stencil := false };
            let _ <- Gl.clear ctx mask;
            let _ <- Gl.enable ctx GlCap.depth_test;
            let _ <- Gl.use_program ctx program;
            let _ <- Gl.uniform1f ctx time t;
            let _ <- Gl.draw_arrays ctx GlPrimitive.triangles 0 3;
            return (Option.some Msg.drew)
        },
    }

def run (fx : Fx) : IO (Option Msg) :=
    match fx {
        Fx.setup => setup,
        Fx.draw s t => draw s t,
    }

def host : Host IO Fx Msg := Host.host run

#[export "c"]
def oak_mount : IO Unit := Runtime.mount app

#[export "c"]
def oak_dispatch_event (handler : I64) : IO Unit := Runtime.dispatch handler

#[export "c"]
def oak_tick : IO Unit := Runtime.tick app host

def main : IO Unit := IO.pure unit
