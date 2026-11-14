// A spinning, textured quad drawn with WebGL from an Oak program.
//
// The update stays pure: every animation frame returns its drawing as a
// `Command.after_render` effect, which `oak_wasm` runs after the patch, so
// the `<canvas>` the view renders already exists. The first frame's effect
// builds the scene (context, program, buffers, texture) and sends it back as
// a message; later frames draw it and send nothing back.
//
// The geometry, indices and texels are `std::buf` buffers (`Gl.f32_buf`,
// `i32_buf`, `u8_buf`); the per-frame aspect correction is a mat4 uniform,
// and the rotation happens in the vertex shader from `u_time`.
//
// Build and serve. The output goes under `target-monad/` (gitignored); the
// page needs the web host's JS beside the wasm (`scripts/gen-web-js.sh`
// writes `wasm/web/web.js` if it is missing):
//
//     out="$PWD/target-monad/web/oak_webgl"   # `-o` must be absolute
//     monad build --target wasm32-unknown-unknown examples/oak_webgl.mo -o "$out/app.wasm"
//     cp wasm/web/web.js wasm/web/web_runtime.js wasm/web/float_format.js "$out/"
//     python3 -m http.server 8001 -d "$out"
//
// with this `index.html` in `$out`:
//
//     <div id="app"></div>
//     <script type="module">
//       import { start } from './web.js';
//       start('./app.wasm', '#app');
//     </script>
#![mote { name := "oak_webgl_example", deps := [oak, oak_wasm, web_wasm, web_event] }]

use oak::typed {Oak.Node}
use oak::elements {Html.canvas, Html.div, Html.id_, Html.key, Html.span, Html.style_attr, Html.text}
use oak::events {Subscription}
use oak::app {Command, Host, Program}
use oak_wasm::program {Runtime.dispatch, Runtime.mount, Runtime.tick}
use web_event::event {WebEvent}
use web_wasm::dom {Dom.query}
use web_wasm::canvas {Canvas.buffer_size, Canvas.fit}
use web_wasm::gl {
    GlContext, GlProgram, GlUniform, GlOptions.default, GlBufferTarget, GlUsage, GlAttribType,
    GlPrimitive, GlTextureTarget, GlFilter, GlWrap, GlClear, Gl.context, Gl.program,
    Gl.use_program, Gl.attrib_location, Gl.uniform_location, Gl.uniform1f, Gl.uniform1i,
    Gl.create_buffer, Gl.bind_buffer, Gl.vertex_attrib_pointer, Gl.enable_vertex_attrib,
    Gl.viewport, Gl.clear_color, Gl.clear, Gl.draw_elements, Gl.create_texture,
    Gl.bind_texture, Gl.active_texture, Gl.tex_filter, Gl.tex_wrap, Gl.drawing_buffer_size,
    Gl.has_uint_indices, Gl.buffer_data_f32, Gl.buffer_data_i32, Gl.uniform_matrix4,
    Gl.tex_image_rgba, Gl.f32_buf, Gl.i32_buf, Gl.u8_buf,
}

/// The handles the model keeps once setup succeeds.
struct Scene {
    ctx : GlContext,
    program : GlProgram,
    time : GlUniform,
    aspect : GlUniform
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
    ready (scene : Scene),
    failed (error : String)
}

struct Model {
    status : String,
    scene : Option Scene,
    setting_up : Bool
}

def init : Model := { status := "starting", scene := Option.none, setting_up := false }

def on_frame (status : String) (scene : Option Scene) (setting_up : Bool) (t : F64)
    : Pair Model (Command Fx Msg) :=
    match scene {
        Option.some s =>
            let m : Model := { status := status, scene := Option.some s, setting_up := false } in
            Pair.pair m (Command.after_render (Fx.draw s t)),
        Option.none =>
            let m : Model := { status := status, scene := Option.none, setting_up := true } in
            if setting_up then Pair.pair m Command.none else Pair.pair m (Command.after_render Fx.setup),
    }

def update (model : Model) (msg : Msg) : Pair Model (Command Fx Msg) :=
    match model {
        { status, scene, setting_up } =>
            match msg {
                Msg.frame t => on_frame status scene setting_up t,
                Msg.ready s =>
                    let m : Model := { status := "drawing", scene := Option.some s, setting_up := false } in
                    Pair.pair m Command.none,
                Msg.failed e =>
                    let m : Model := { status := String.concat "failed: " e, scene := scene,
                        setting_up := true } in
                    Pair.pair m Command.none,
            },
    }

def subs (_m : Model) : List (Subscription Msg) :=
    [Subscription.animation_frame (fn (e : WebEvent) => Msg.frame e.time_stamp)]

/// The canvas is keyed so a re-render keeps the same node (and context).
def view (m : Model) : Oak.Node Msg :=
    Html.div [Html.id_ "scene"]
        [Html.canvas [Html.id_ "board", Html.key "board",
            Html.style_attr "width: 100%; height: 360px; display: block"] List.empty,
            Html.span [Html.id_ "status"] [Html.text m.status]]

def app : Program Model Msg Fx := Program.with_subs init update view subs

// ─── The host: the only place that touches WebGL ─────────────────────

def vertex_source : String :=
    String.concat_list [
        "attribute vec2 a_position; attribute vec2 a_uv; uniform float u_time; uniform mat4 u_aspect; ",
        "varying vec2 v_uv; void main() { float a = u_time * 0.001; ",
        "mat2 r = mat2(cos(a), sin(a), -sin(a), cos(a)); v_uv = a_uv; ",
        "gl_Position = u_aspect * vec4(r * a_position, 0.0, 1.0); }",
    ]

def fragment_source : String :=
    "precision mediump float; varying vec2 v_uv; uniform sampler2D u_tex; void main() { gl_FragColor = texture2D(u_tex, v_uv); }"

/// x, y, u, v per corner: 16 bytes a vertex.
def quad : List F64 :=
    [-0.6, -0.6, 0.0, 0.0, 0.6, -0.6, 1.0, 0.0, 0.6, 0.6, 1.0, 1.0, -0.6, 0.6, 0.0, 1.0]

def quad_indices : List I64 := [0, 1, 2, 0, 2, 3]

/// One RGBA texel of an 8x8 checkerboard.
def texel (i : I64) : List I64 :=
    let x := I64.rem i 8 in
    let y := i / 8 in
    if I64.beq (I64.rem (x + y) 2) 0 then [240, 200, 80, 255] else [40, 60, 120, 255]

#[terminating]
def checker_from (i : I64) : List I64 :=
    if I64.lt i 64 then List.append (texel i) (checker_from (i + 1)) else List.empty

def attrib (ctx : GlContext) (p : GlProgram) (name : String) (offset : I64) : IO Unit := do {
    let loc <- Gl.attrib_location ctx p name;
    match loc {
        Option.some i => do {
            let _ <- Gl.vertex_attrib_pointer ctx i 2 GlAttribType.f32 false 16 offset;
            Gl.enable_vertex_attrib ctx i
        },
        Option.none => IO.pure unit,
    }
}

def upload_geometry (ctx : GlContext) (p : GlProgram) : IO Unit := do {
    let vb <- Gl.create_buffer ctx;
    let _ <- Gl.bind_buffer ctx GlBufferTarget.array vb;
    let verts <- Gl.f32_buf quad;
    let _ <- Gl.buffer_data_f32 ctx GlBufferTarget.array (Shared.of verts) GlUsage.static_draw;
    let ib <- Gl.create_buffer ctx;
    let _ <- Gl.bind_buffer ctx GlBufferTarget.element_array ib;
    let idx <- Gl.i32_buf quad_indices;
    let _ <- Gl.buffer_data_i32 ctx GlBufferTarget.element_array (Shared.of idx) GlUsage.static_draw;
    let _ <- attrib ctx p "a_position" 0;
    attrib ctx p "a_uv" 8
}

def upload_texture (ctx : GlContext) : IO Unit := do {
    let tex <- Gl.create_texture ctx;
    let _ <- Gl.active_texture ctx 0;
    let _ <- Gl.bind_texture ctx GlTextureTarget.texture_2d tex;
    let _ <- Gl.tex_filter ctx GlTextureTarget.texture_2d GlFilter.nearest GlFilter.nearest;
    let _ <- Gl.tex_wrap ctx GlTextureTarget.texture_2d GlWrap.clamp_to_edge GlWrap.clamp_to_edge;
    let px <- Gl.u8_buf (checker_from 0);
    let _ <- Gl.tex_image_rgba ctx GlTextureTarget.texture_2d 8 8 (Shared.of px);
    IO.pure unit
}

def scene_of (ctx : GlContext) (p : GlProgram) (time : Option GlUniform) (aspect : Option GlUniform)
    : Option Msg :=
    match time {
        Option.some t =>
            match aspect {
                Option.some a =>
                    let s : Scene := { ctx := ctx, program := p, time := t, aspect := a } in
                    Option.some (Msg.ready s),
                Option.none => Option.some (Msg.failed "no u_aspect"),
            },
        Option.none => Option.some (Msg.failed "no u_time"),
    }

/// Point the sampler at texture unit 0.
def bind_sampler (ctx : GlContext) (sampler : Option GlUniform) : IO Unit :=
    match sampler {
        Option.some u => Gl.uniform1i ctx u 0,
        Option.none => IO.pure unit,
    }

def build (ctx : GlContext) (p : GlProgram) : IO (Option Msg) := do {
    let _ <- Gl.use_program ctx p;
    let _ <- upload_geometry ctx p;
    let _ <- upload_texture ctx;
    let sampler <- Gl.uniform_location ctx p "u_tex";
    let _ <- bind_sampler ctx sampler;
    let time <- Gl.uniform_location ctx p "u_time";
    let aspect <- Gl.uniform_location ctx p "u_aspect";
    return (scene_of ctx p time aspect)
}

def setup_with (ctx : GlContext) : IO (Option Msg) := do {
    let uint <- Gl.has_uint_indices ctx;
    let built <- Gl.program ctx vertex_source fragment_source;
    match built {
        Result.err e => return (Option.some (Msg.failed e)),
        Result.ok p => if uint then build ctx p else IO.pure (Option.some (Msg.failed "no 32-bit indices")),
    }
}

def setup : IO (Option Msg) := do {
    let canvas <- Dom.query "#board";
    let _ <- Canvas.fit canvas;
    let found <- Gl.context canvas GlOptions.default;
    match found {
        Option.none => return (Option.some (Msg.failed "no WebGL")),
        Option.some ctx => setup_with ctx,
    }
}

/// Scale x by height/width so the quad stays square (column-major mat4).
def aspect_matrix (size : Pair F64 F64) : List F64 :=
    match size {
        Pair.pair w h =>
            let sx := if F64.gt w 0.0 then h / w else 1.0 in
            [sx, 0.0, 0.0, 0.0, 0.0, 1.0, 0.0, 0.0, 0.0, 0.0, 1.0, 0.0, 0.0, 0.0, 0.0, 1.0],
    }

def viewport_to (ctx : GlContext) (size : Pair I64 I64) : IO Unit :=
    match size { Pair.pair w h => Gl.viewport ctx 0 0 w h }

def draw (s : Scene) (t : F64) : IO (Option Msg) :=
    match s {
        { ctx, program, time, aspect } => do {
            // Refit every frame: a window resize changes the layout size.
            let canvas <- Dom.query "#board";
            let _ <- Canvas.fit canvas;
            let buffer <- Canvas.buffer_size canvas;
            let size <- Gl.drawing_buffer_size ctx;
            let _ <- viewport_to ctx size;
            let _ <- Gl.clear_color ctx 0.08 0.09 0.12 1.0;
            let mask : GlClear := { color := true, depth := false, stencil := false };
            let _ <- Gl.clear ctx mask;
            let _ <- Gl.use_program ctx program;
            let _ <- Gl.uniform1f ctx time t;
            let m <- Gl.f32_buf (aspect_matrix buffer);
            let _ <- Gl.uniform_matrix4 ctx aspect (Shared.of m);
            let _ <- Gl.draw_elements ctx GlPrimitive.triangles 6 0;
            return Option.none
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
