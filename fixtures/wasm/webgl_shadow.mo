// Render targets, without Oak: the shape of a shadow-map pass.
//
// `main` allocates a 512x512 depth texture, attaches it to a framebuffer
// and checks the framebuffer is complete. It then draws one triangle into
// it with colour writes off and a polygon offset (the depth pass), binds
// the canvas again and draws a full-screen quad that samples the depth
// texture. Without depth textures (WebGL1 lacking `WEBGL_depth_texture`)
// `Gl.tex_image_depth` says no and the depth pass is skipped.
// `wasm/web/smoke/webgl_shadow_smoke.mjs` checks the report and the stream.
#![mote { name := "webgl_shadow", deps := [web_wasm] }]

use web_wasm::dom {Dom.append, Dom.create, Dom.root, Dom.set_attr, Dom.text_node}
use web_wasm::gl {
    GlContext, GlProgram, GlTexture, GlOptions.default, GlBufferTarget, GlUsage, GlAttribType,
    GlPrimitive, GlTextureTarget, GlFilter, GlWrap, GlCap, GlAttachment, GlClear, Gl.context,
    Gl.program, Gl.use_program, Gl.attrib_location, Gl.uniform_location, Gl.uniform1i,
    Gl.create_buffer, Gl.bind_buffer, Gl.vertex_attrib_pointer, Gl.enable_vertex_attrib,
    Gl.buffer_data_f32, Gl.f32_buf, Gl.draw_arrays, Gl.create_texture, Gl.bind_texture,
    Gl.active_texture, Gl.tex_filter, Gl.tex_wrap, Gl.viewport, Gl.clear, Gl.enable, Gl.disable,
    Gl.create_framebuffer, Gl.bind_framebuffer, Gl.bind_default_framebuffer,
    Gl.delete_framebuffer, Gl.has_depth_texture, Gl.tex_image_depth, Gl.framebuffer_texture,
    Gl.framebuffer_complete, Gl.color_mask, Gl.polygon_offset,
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

def depth_vertex : String :=
    "attribute vec2 a_position; void main() { gl_Position = vec4(a_position * 0.8, 0.5, 1.0); }"

def depth_fragment : String :=
    "precision mediump float; void main() { gl_FragColor = vec4(1.0); }"

def quad_vertex : String :=
    "attribute vec2 a_position; varying vec2 v_uv; void main() { v_uv = a_position * 0.5 + 0.5; gl_Position = vec4(a_position, 0.0, 1.0); }"

def quad_fragment : String :=
    "precision mediump float; uniform sampler2D u_shadow; varying vec2 v_uv; void main() { float d = texture2D(u_shadow, v_uv).r; gl_FragColor = vec4(vec3(d), 1.0); }"

/// A full-screen triangle strip; the depth pass draws its first three
/// vertices.
def upload_quad (ctx : GlContext) : IO Bool := do {
    let vb <- Gl.create_buffer ctx;
    let _ <- Gl.bind_buffer ctx GlBufferTarget.array vb;
    let verts <- Gl.f32_buf [-1.0, -1.0, 1.0, -1.0, -1.0, 1.0, 1.0, 1.0];
    Gl.buffer_data_f32 ctx GlBufferTarget.array (Shared.of verts) GlUsage.static_draw
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

/// The depth texture: nearest filtering, clamped, 512x512. A zero size is
/// refused before the host.
def make_depth_texture (ctx : GlContext) (tex : GlTexture) : IO String := do {
    let t := GlTextureTarget.texture_2d;
    let _ <- Gl.bind_texture ctx t tex;
    let _ <- Gl.tex_filter ctx t GlFilter.nearest GlFilter.nearest;
    let _ <- Gl.tex_wrap ctx t GlWrap.clamp_to_edge GlWrap.clamp_to_edge;
    let zero <- Gl.tex_image_depth ctx 0 0;
    let ok <- Gl.tex_image_depth ctx 512 512;
    return (String.concat_list ["zero_size=", yes_no zero, " depth=", yes_no ok])
}

def depth_pass (ctx : GlContext) (p : GlProgram) : IO Unit := do {
    let _ <- Gl.viewport ctx 0 0 512 512;
    let _ <- Gl.color_mask ctx false false false false;
    let _ <- Gl.enable ctx GlCap.depth_test;
    let _ <- Gl.enable ctx GlCap.polygon_offset_fill;
    let _ <- Gl.polygon_offset ctx 2.0 4.0;
    let only_depth : GlClear := { color := false, depth := true };
    let _ <- Gl.clear ctx only_depth;
    let _ <- Gl.use_program ctx p;
    let _ <- bind_position ctx p;
    let _ <- Gl.draw_arrays ctx GlPrimitive.triangles 0 3;
    let _ <- Gl.disable ctx GlCap.polygon_offset_fill;
    Gl.color_mask ctx true true true true
}

def sample_shadow (ctx : GlContext) (p : GlProgram) : IO Unit := do {
    let u <- Gl.uniform_location ctx p "u_shadow";
    match u {
        Option.some loc => Gl.uniform1i ctx loc 0,
        Option.none => IO.pure unit,
    }
}

def quad_pass (ctx : GlContext) (p : GlProgram) (tex : GlTexture) : IO Unit := do {
    let _ <- Gl.viewport ctx 0 0 640 400;
    let _ <- Gl.use_program ctx p;
    let _ <- bind_position ctx p;
    let _ <- Gl.active_texture ctx 0;
    let _ <- Gl.bind_texture ctx GlTextureTarget.texture_2d tex;
    let _ <- sample_shadow ctx p;
    Gl.draw_arrays ctx GlPrimitive.triangle_strip 0 4
}

/// The framebuffer around `tex`; draws only when it is complete.
def with_target (ctx : GlContext) (depth : GlProgram) (quad : GlProgram) (tex : GlTexture)
    : IO String := do {
    let fb <- Gl.create_framebuffer ctx;
    let _ <- Gl.bind_framebuffer ctx fb;
    let _ <- Gl.framebuffer_texture ctx GlAttachment.depth tex;
    let complete <- Gl.framebuffer_complete ctx;
    let _ <- if complete then depth_pass ctx depth else IO.pure unit;
    let _ <- Gl.bind_default_framebuffer ctx;
    let _ <- if complete then quad_pass ctx quad tex else IO.pure unit;
    let _ <- Gl.delete_framebuffer ctx fb;
    return (String.concat " complete=" (yes_no complete))
}

def run_programs (ctx : GlContext) (depth : GlProgram) (quad : GlProgram) : IO Unit := do {
    let has <- Gl.has_depth_texture ctx;
    let quad_ok <- upload_quad ctx;
    let tex <- Gl.create_texture ctx;
    let made <- make_depth_texture ctx tex;
    let drawn <- if has then with_target ctx depth quad tex else IO.pure " skipped";
    report (String.concat_list ["has_depth=", yes_no has, " quad=", yes_no quad_ok, " ", made, drawn])
}

def with_quad_program (ctx : GlContext) (depth : GlProgram) : IO Unit := do {
    let built <- Gl.program ctx quad_vertex quad_fragment;
    match built {
        Result.ok quad => run_programs ctx depth quad,
        Result.err e => report (String.concat "quad program: " e),
    }
}

def run (ctx : GlContext) : IO Unit := do {
    let built <- Gl.program ctx depth_vertex depth_fragment;
    match built {
        Result.ok depth => with_quad_program ctx depth,
        Result.err e => report (String.concat "depth program: " e),
    }
}

def main : IO Unit := do {
    let root <- Dom.root;
    let canvas <- Dom.create "canvas";
    let _ <- Dom.set_attr canvas "width" "640";
    let _ <- Dom.set_attr canvas "height" "400";
    let _ <- Dom.append root canvas;
    let found <- Gl.context canvas GlOptions.default;
    match found {
        Option.none => report "no webgl",
        Option.some ctx => run ctx,
    }
}
