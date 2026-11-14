// Buffered drawing through `std::buf`, without Oak: a vertex buffer from a
// `Buf F32`, an index buffer from a `Buf I32`, a mat4 uniform, an RGBA
// texture from a `Buf U8`, and `drawElements`.
//
// It also checks the refusals: a matrix buffer shorter than 16 floats and a
// pixel buffer shorter than w*h*4 bytes are rejected by the runtime before
// the host sees them, so neither reaches the GL stream.
// `wasm/web/webgl_triangle_smoke.mjs` compares the stream to a golden.
#![mote { name := "webgl_triangle", deps := [web_wasm] }]

use web_wasm::dom {Dom.append, Dom.create, Dom.root, Dom.set_attr, Dom.text_node}
use web_wasm::gl {
    GlContext, GlProgram, GlUniform, GlOptions.default, GlBufferTarget, GlUsage, GlAttribType,
    GlPrimitive, GlTextureTarget, Gl.context, Gl.program, Gl.use_program, Gl.attrib_location,
    Gl.uniform_location, Gl.create_buffer, Gl.bind_buffer, Gl.vertex_attrib_pointer,
    Gl.enable_vertex_attrib, Gl.draw_elements, Gl.create_texture, Gl.bind_texture,
    Gl.has_uint_indices, Gl.buffer_data_f32, Gl.buffer_data_i32, Gl.buffer_sub_data_f32,
    Gl.uniform_matrix4, Gl.tex_image_rgba, Gl.f32_buf, Gl.i32_buf, Gl.u8_buf,
}

def report (text : String) : IO Unit := do {
    let root <- Dom.root;
    let span <- Dom.create "span";
    let _ <- Dom.set_attr span "id" "report";
    let t <- Dom.text_node text;
    let _ <- Dom.append span t;
    Dom.append root span
}

def yes_no (b : Bool) : String := if b then "yes" else "no"

def vertex_source : String :=
    "attribute vec2 a_position; uniform mat4 u_mvp; void main() { gl_Position = u_mvp * vec4(a_position, 0.0, 1.0); }"

def fragment_source : String :=
    "precision mediump float; uniform sampler2D u_tex; void main() { gl_FragColor = texture2D(u_tex, vec2(0.5)); }"

def identity : List F64 :=
    [1.0, 0.0, 0.0, 0.0, 0.0, 1.0, 0.0, 0.0, 0.0, 0.0, 1.0, 0.0, 0.0, 0.0, 0.0, 1.0]

/// Vertices, then indices: both upload into freshly bound buffers.
def upload_geometry (ctx : GlContext) : IO String := do {
    let vb <- Gl.create_buffer ctx;
    let _ <- Gl.bind_buffer ctx GlBufferTarget.array vb;
    let verts <- Gl.f32_buf [0.0, 0.5, -0.5, -0.5, 0.5, -0.5];
    let sv := Shared.of verts;
    let v_ok <- Gl.buffer_data_f32 ctx GlBufferTarget.array sv GlUsage.static_draw;
    let tip <- Gl.f32_buf [0.25, 0.75];
    let sub_ok <- Gl.buffer_sub_data_f32 ctx GlBufferTarget.array 0 (Shared.of tip);
    let ib <- Gl.create_buffer ctx;
    let _ <- Gl.bind_buffer ctx GlBufferTarget.element_array ib;
    let idx <- Gl.i32_buf [0, 1, 2];
    let i_ok <- Gl.buffer_data_i32 ctx GlBufferTarget.element_array (Shared.of idx) GlUsage.static_draw;
    return (String.concat_list [" vertices=", yes_no v_ok, " sub=", yes_no sub_ok, " indices=", yes_no i_ok])
}

def bind_position (ctx : GlContext) (p : GlProgram) : IO Unit := do {
    let loc <- Gl.attrib_location ctx p "a_position";
    match loc {
        Option.some i => do {
            let _ <- Gl.vertex_attrib_pointer ctx i 2 GlAttribType.f32 false 0 0;
            Gl.enable_vertex_attrib ctx i
        },
        Option.none => IO.pure unit,
    }
}

/// A full mat4 is accepted; an 8-float buffer is refused before the host.
def set_matrix (ctx : GlContext) (u : GlUniform) : IO String := do {
    let m <- Gl.f32_buf identity;
    let ok <- Gl.uniform_matrix4 ctx u (Shared.of m);
    let short <- Gl.f32_buf [1.0, 0.0, 0.0, 0.0, 0.0, 1.0, 0.0, 0.0];
    let refused <- Gl.uniform_matrix4 ctx u (Shared.of short);
    return (String.concat_list [" mat4=", yes_no ok, " short_mat4=", yes_no refused])
}

def set_matrix_at (ctx : GlContext) (p : GlProgram) : IO String := do {
    let u <- Gl.uniform_location ctx p "u_mvp";
    match u {
        Option.some loc => set_matrix ctx loc,
        Option.none => IO.pure " mat4=missing",
    }
}

/// 2x1 RGBA; 300 masks to 44. A 2x2 upload from the same 8 bytes is refused.
def upload_texture (ctx : GlContext) : IO String := do {
    let tex <- Gl.create_texture ctx;
    let _ <- Gl.bind_texture ctx GlTextureTarget.texture_2d tex;
    let px <- Gl.u8_buf [255, 0, 0, 255, 0, 300, 0, 255];
    let sp := Shared.of px;
    let ok <- Gl.tex_image_rgba ctx GlTextureTarget.texture_2d 2 1 sp;
    let refused <- Gl.tex_image_rgba ctx GlTextureTarget.texture_2d 2 2 sp;
    return (String.concat_list [" texture=", yes_no ok, " short_texture=", yes_no refused])
}

def draw_with (ctx : GlContext) (p : GlProgram) : IO Unit := do {
    let geometry <- upload_geometry ctx;
    let _ <- Gl.use_program ctx p;
    let _ <- bind_position ctx p;
    let matrix <- set_matrix_at ctx p;
    let texture <- upload_texture ctx;
    let uint <- Gl.has_uint_indices ctx;
    let _ <- Gl.draw_elements ctx GlPrimitive.triangles 3 0;
    report (String.concat_list ["uint=", yes_no uint, geometry, matrix, texture])
}

def run (ctx : GlContext) : IO Unit := do {
    let built <- Gl.program ctx vertex_source fragment_source;
    match built {
        Result.ok p => draw_with ctx p,
        Result.err e => report (String.concat "program: " e),
    }
}

def main : IO Unit := do {
    let root <- Dom.root;
    let canvas <- Dom.create "canvas";
    let _ <- Dom.append root canvas;
    let found <- Gl.context canvas GlOptions.default;
    match found {
        Option.none => report "no webgl",
        Option.some ctx => run ctx,
    }
}
