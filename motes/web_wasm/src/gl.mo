/// WebGL (and WebGL2) for the web target.
///
/// A context comes from a `<canvas>` node: `Gl.context` asks the host for
/// `webgl2` and falls back to `webgl`, and `Gl.version` says which one it
/// got. Every GL object is an id into the JS host's table, wrapped in a
/// one-field struct here so a buffer cannot be passed where a texture is
/// expected. The handles are `Copy`: an id is a plain number, and a frame
/// names the same context and objects many times.
///
/// GL enum values appear only in this file, in the `*.code` functions; the
/// boundary carries plain I64 words. Integer state calls share one
/// `gl_state` import whose selector numbers are `GlState.code`, mirrored by
/// `host.gl_state` in `wasm/web/web_runtime.js`.
///
/// Bulk uploads (`bufferData`, `uniformMatrix4fv`, RGBA `texImage2D`) wait
/// for `std::buf`'s typed `Buf F32`/`Buf I32`/`Buf U8` to reach main
/// (`plans/implementations/web-webgl.md`, Part B). Textures can already be
/// filled from a loaded image (`GlImage`).

use lib::types {Node}
use lib::ffi {
    canvas_get_context_raw, gl_info_raw, gl_create_raw, gl_delete_raw, gl_bind_raw,
    gl_shader_raw, gl_link_raw, gl_log_raw, gl_location_raw, gl_vertex_attrib_raw,
    gl_uniform_f_raw, gl_clear_color_raw, gl_state_raw, gl_draw_raw,
    gl_tex_image_from_image_raw, image_load_begin_raw, image_info_raw,
}

// ─── Handles ─────────────────────────────────────────────────────────

pub struct GlContext {
    id : I64
}

pub struct GlShader {
    id : I64
}

pub struct GlProgram {
    id : I64
}

pub struct GlBuffer {
    id : I64
}

pub struct GlTexture {
    id : I64
}

pub struct GlVertexArray {
    id : I64
}

pub struct GlUniform {
    id : I64
}

/// An image loading for use as a texture (`GlImage.load`).
pub struct GlImage {
    id : I64
}

pub instance Copy GlContext {
    def copy (c : GlContext) : Pair GlContext GlContext := Pair.pair c c
}

pub instance Copy GlShader {
    def copy (s : GlShader) : Pair GlShader GlShader := Pair.pair s s
}

pub instance Copy GlProgram {
    def copy (p : GlProgram) : Pair GlProgram GlProgram := Pair.pair p p
}

pub instance Copy GlBuffer {
    def copy (b : GlBuffer) : Pair GlBuffer GlBuffer := Pair.pair b b
}

pub instance Copy GlTexture {
    def copy (t : GlTexture) : Pair GlTexture GlTexture := Pair.pair t t
}

pub instance Copy GlVertexArray {
    def copy (v : GlVertexArray) : Pair GlVertexArray GlVertexArray := Pair.pair v v
}

pub instance Copy GlUniform {
    def copy (u : GlUniform) : Pair GlUniform GlUniform := Pair.pair u u
}

pub instance Copy GlImage {
    def copy (i : GlImage) : Pair GlImage GlImage := Pair.pair i i
}

// ─── Context options ─────────────────────────────────────────────────

/// `getContext` attributes. `webgl1_only` skips the WebGL2 attempt (for
/// testing the fallback path).
pub struct GlOptions {
    alpha : Bool := true,
    antialias : Bool := true,
    depth : Bool := true,
    stencil : Bool := false,
    premultiplied_alpha : Bool := true,
    preserve_drawing_buffer : Bool := false,
    webgl1_only : Bool := false
}

/// The browser defaults.
pub def GlOptions.default : GlOptions :=
    let o : GlOptions := {
        alpha := true, antialias := true, depth := true, stencil := false,
        premultiplied_alpha := true, preserve_drawing_buffer := false, webgl1_only := false
    } in
    o

def bit (on : Bool) (value : I64) : I64 := if on then value else 0

/// The flag word `host.canvas_get_context` decodes.
pub def GlOptions.flags (o : GlOptions) : I64 :=
    match o {
        { alpha, antialias, depth, stencil, premultiplied_alpha, preserve_drawing_buffer,
            webgl1_only } =>
            bit alpha 1 + bit antialias 2 + bit depth 4 + bit stencil 8
                + bit premultiplied_alpha 16 + bit preserve_drawing_buffer 32
                + bit webgl1_only 64,
    }

// ─── Enums ───────────────────────────────────────────────────────────

pub type GlShaderStage { vertex, fragment }

pub def GlShaderStage.code (s : GlShaderStage) : I64 :=
    match s {
        GlShaderStage.vertex => 35633,
        GlShaderStage.fragment => 35632,
    }

pub type GlBufferTarget { array, element_array }

pub def GlBufferTarget.code (t : GlBufferTarget) : I64 :=
    match t {
        GlBufferTarget.array => 34962,
        GlBufferTarget.element_array => 34963,
    }

pub type GlTextureTarget { texture_2d }

pub def GlTextureTarget.code (t : GlTextureTarget) : I64 :=
    match t {
        GlTextureTarget.texture_2d => 3553,
    }

pub type GlUsage { static_draw, dynamic_draw, stream_draw }

pub def GlUsage.code (u : GlUsage) : I64 :=
    match u {
        GlUsage.static_draw => 35044,
        GlUsage.dynamic_draw => 35048,
        GlUsage.stream_draw => 35040,
    }

pub type GlPrimitive { points, lines, line_loop, line_strip, triangles, triangle_strip, triangle_fan }

pub def GlPrimitive.code (p : GlPrimitive) : I64 :=
    match p {
        GlPrimitive.points => 0,
        GlPrimitive.lines => 1,
        GlPrimitive.line_loop => 2,
        GlPrimitive.line_strip => 3,
        GlPrimitive.triangles => 4,
        GlPrimitive.triangle_strip => 5,
        GlPrimitive.triangle_fan => 6,
    }

pub type GlCap { blend, cull_face, depth_test, scissor_test, stencil_test, polygon_offset_fill }

pub def GlCap.code (c : GlCap) : I64 :=
    match c {
        GlCap.blend => 3042,
        GlCap.cull_face => 2884,
        GlCap.depth_test => 2929,
        GlCap.scissor_test => 3089,
        GlCap.stencil_test => 2960,
        GlCap.polygon_offset_fill => 32823,
    }

pub type GlBlendFactor {
    zero, one, src_color, one_minus_src_color, src_alpha, one_minus_src_alpha,
    dst_alpha, one_minus_dst_alpha
}

pub def GlBlendFactor.code (f : GlBlendFactor) : I64 :=
    match f {
        GlBlendFactor.zero => 0,
        GlBlendFactor.one => 1,
        GlBlendFactor.src_color => 768,
        GlBlendFactor.one_minus_src_color => 769,
        GlBlendFactor.src_alpha => 770,
        GlBlendFactor.one_minus_src_alpha => 771,
        GlBlendFactor.dst_alpha => 772,
        GlBlendFactor.one_minus_dst_alpha => 773,
    }

/// A depth comparison (`depthFunc`).
pub type GlCompare { never, less, equal, lequal, greater, notequal, gequal, always }

pub def GlCompare.code (c : GlCompare) : I64 :=
    match c {
        GlCompare.never => 512,
        GlCompare.less => 513,
        GlCompare.equal => 514,
        GlCompare.lequal => 515,
        GlCompare.greater => 516,
        GlCompare.notequal => 517,
        GlCompare.gequal => 518,
        GlCompare.always => 519,
    }

pub type GlFace { front, back, front_and_back }

pub def GlFace.code (f : GlFace) : I64 :=
    match f {
        GlFace.front => 1028,
        GlFace.back => 1029,
        GlFace.front_and_back => 1032,
    }

pub type GlWinding { cw, ccw }

pub def GlWinding.code (w : GlWinding) : I64 :=
    match w {
        GlWinding.cw => 2304,
        GlWinding.ccw => 2305,
    }

/// A vertex attribute's component type.
pub type GlAttribType { f32, u8, u16, i8, i16 }

pub def GlAttribType.code (t : GlAttribType) : I64 :=
    match t {
        GlAttribType.f32 => 5126,
        GlAttribType.u8 => 5121,
        GlAttribType.u16 => 5123,
        GlAttribType.i8 => 5120,
        GlAttribType.i16 => 5122,
    }

pub type GlFilter { nearest, linear, nearest_mipmap_nearest, linear_mipmap_nearest, nearest_mipmap_linear, linear_mipmap_linear }

pub def GlFilter.code (f : GlFilter) : I64 :=
    match f {
        GlFilter.nearest => 9728,
        GlFilter.linear => 9729,
        GlFilter.nearest_mipmap_nearest => 9984,
        GlFilter.linear_mipmap_nearest => 9985,
        GlFilter.nearest_mipmap_linear => 9986,
        GlFilter.linear_mipmap_linear => 9987,
    }

pub type GlWrap { repeat, clamp_to_edge, mirrored_repeat }

pub def GlWrap.code (w : GlWrap) : I64 :=
    match w {
        GlWrap.repeat => 10497,
        GlWrap.clamp_to_edge => 33071,
        GlWrap.mirrored_repeat => 33648,
    }

/// Which buffers `Gl.clear` clears.
pub struct GlClear {
    color : Bool := true,
    depth : Bool := false,
    stencil : Bool := false
}

pub def GlClear.code (c : GlClear) : I64 :=
    match c {
        { color, depth, stencil } => bit color 16384 + bit depth 256 + bit stencil 1024,
    }

/// The `gl_state` selector (`host.gl_state`'s switch).
type GlState {
    viewport, clear, cap, blend_func, depth_func, cull_face, front_face, depth_mask,
    active_texture, generate_mipmap, tex_parameter, pixel_store, attrib_array, uniform_i
}

def GlState.code (s : GlState) : I64 :=
    match s {
        GlState.viewport => 0,
        GlState.clear => 1,
        GlState.cap => 2,
        GlState.blend_func => 3,
        GlState.depth_func => 4,
        GlState.cull_face => 5,
        GlState.front_face => 6,
        GlState.depth_mask => 7,
        GlState.active_texture => 8,
        GlState.generate_mipmap => 9,
        GlState.tex_parameter => 10,
        GlState.pixel_store => 11,
        GlState.attrib_array => 12,
        GlState.uniform_i => 13,
    }

/// The `gl_create`/`gl_delete`/`gl_bind` object kinds (`GL_KIND_*` in the
/// JS host).
type GlKind { buffer, texture, vertex_array, program, shader }

def GlKind.code (k : GlKind) : I64 :=
    match k {
        GlKind.buffer => 0,
        GlKind.texture => 1,
        GlKind.vertex_array => 2,
        GlKind.program => 3,
        GlKind.shader => 4,
    }

def state (ctx : GlContext) (s : GlState) (a : I64) (b : I64) (c : I64) (d : I64) : IO Unit :=
    IO.mk (gl_state_raw ctx.id (GlState.code s) a b c d)

def info (ctx : GlContext) (which : I64) : IO I64 := IO.mk (gl_info_raw ctx.id which)

// ─── Context ─────────────────────────────────────────────────────────

/// A rendering context for `canvas`: WebGL2 when the browser has it,
/// otherwise WebGL1. `none` when the node is not a canvas or WebGL is
/// unavailable. Asking twice for the same canvas returns the same context.
pub def Gl.context (canvas : Node) (opts : GlOptions) : IO (Option GlContext) := do {
    let id <- IO.mk (canvas_get_context_raw canvas (GlOptions.flags opts));
    if I64.lt id 1
    then IO.pure Option.none
    else IO.pure (Option.some { id := id : GlContext })
}

/// 2 for WebGL2, 1 for WebGL1.
pub def Gl.version (ctx : GlContext) : IO I64 := info ctx 0

/// True while the context is lost. Every object made through it is invalid
/// after a loss; rebuild them once the canvas fires `webglcontextrestored`.
pub def Gl.is_lost (ctx : GlContext) : IO Bool := do {
    let lost <- info ctx 1;
    IO.pure (I64.beq lost 1)
}

/// The drawing buffer's actual size in pixels.
pub def Gl.drawing_buffer_size (ctx : GlContext) : IO (Pair I64 I64) := do {
    let w <- info ctx 2;
    let h <- info ctx 3;
    IO.pure (Pair.pair w h)
}

/// `getError`: 0 when no error is pending.
pub def Gl.error (ctx : GlContext) : IO I64 := info ctx 4

/// Whether vertex array objects exist (WebGL2, or WebGL1 with
/// `OES_vertex_array_object`).
pub def Gl.has_vertex_arrays (ctx : GlContext) : IO Bool := do {
    let has <- info ctx 5;
    IO.pure (I64.beq has 1)
}

// ─── Shaders and programs ────────────────────────────────────────────

def last_log : IO String := IO.mk gl_log_raw

def shader_result (id : I64) : IO (Result String GlShader) :=
    if I64.lt id 1
    then do {
        let log <- last_log;
        IO.pure (Result.err log)
    }
    else IO.pure (Result.ok { id := id : GlShader })

/// Compile one shader stage. The error is the driver's info log.
pub def Gl.compile_shader (ctx : GlContext) (stage : GlShaderStage) (source : String)
    : IO (Result String GlShader) := do {
    let id <- IO.mk (gl_shader_raw ctx.id (GlShaderStage.code stage) source);
    shader_result id
}

def link_result (p : GlProgram) (ok : I64) : IO (Result String GlProgram) :=
    if I64.beq ok 1
    then IO.pure (Result.ok p)
    else do {
        let log <- last_log;
        IO.pure (Result.err log)
    }

/// Create a program from two compiled shaders and link it. The error is
/// the link info log; a program that fails to link is deleted. The shaders
/// stay the caller's to delete.
pub def Gl.link_program (ctx : GlContext) (vs : GlShader) (fs : GlShader)
    : IO (Result String GlProgram) := do {
    let pid <- IO.mk (gl_create_raw ctx.id (GlKind.code GlKind.program));
    let p : GlProgram := { id := pid };
    let ok <- IO.mk (gl_link_raw ctx.id pid vs.id fs.id);
    link_result p ok
}

def fragment_failed (ctx : GlContext) (vs : GlShader) (e : String) : IO (Result String GlProgram) := do {
    let _ <- Gl.delete_shader ctx vs;
    IO.pure (Result.err (String.concat "fragment shader: " e))
}

/// Link, then drop both shaders: a linked program keeps what it needs.
def link_and_release (ctx : GlContext) (vs : GlShader) (fs : GlShader) : IO (Result String GlProgram) := do {
    let linked <- Gl.link_program ctx vs fs;
    let _ <- Gl.delete_shader ctx vs;
    let _ <- Gl.delete_shader ctx fs;
    IO.pure linked
}

def program_with_vs (ctx : GlContext) (vs : GlShader) (fs_source : String)
    : IO (Result String GlProgram) := do {
    let fr <- Gl.compile_shader ctx GlShaderStage.fragment fs_source;
    match fr {
        Result.err e => fragment_failed ctx vs e,
        Result.ok fs => link_and_release ctx vs fs,
    }
}

/// Compile both stages, link them, and delete the shaders: the usual way to
/// build a program.
pub def Gl.program (ctx : GlContext) (vs_source : String) (fs_source : String)
    : IO (Result String GlProgram) := do {
    let vr <- Gl.compile_shader ctx GlShaderStage.vertex vs_source;
    match vr {
        Result.err e => IO.pure (Result.err (String.concat "vertex shader: " e)),
        Result.ok vs => program_with_vs ctx vs fs_source,
    }
}

pub def Gl.use_program (ctx : GlContext) (p : GlProgram) : IO Unit :=
    IO.mk (gl_bind_raw ctx.id (GlKind.code GlKind.program) 0 p.id)

pub def Gl.delete_program (ctx : GlContext) (p : GlProgram) : IO Unit :=
    IO.mk (gl_delete_raw ctx.id (GlKind.code GlKind.program) p.id)

pub def Gl.delete_shader (ctx : GlContext) (s : GlShader) : IO Unit :=
    IO.mk (gl_delete_raw ctx.id (GlKind.code GlKind.shader) s.id)

/// The attribute index for `name`, or `none` when the linked program has no
/// active attribute by that name.
pub def Gl.attrib_location (ctx : GlContext) (p : GlProgram) (name : String) : IO (Option I64) := do {
    let loc <- IO.mk (gl_location_raw ctx.id p.id 0 name);
    if I64.lt loc 0 then IO.pure Option.none else IO.pure (Option.some loc)
}

/// The uniform location for `name`, or `none` when it is not active. Each
/// call takes a new host table slot: look locations up once, at setup.
pub def Gl.uniform_location (ctx : GlContext) (p : GlProgram) (name : String) : IO (Option GlUniform) := do {
    let id <- IO.mk (gl_location_raw ctx.id p.id 1 name);
    if I64.lt id 1 then IO.pure Option.none else IO.pure (Option.some { id := id : GlUniform })
}

// ─── Uniforms ────────────────────────────────────────────────────────

pub def Gl.uniform1f (ctx : GlContext) (u : GlUniform) (x : F64) : IO Unit :=
    IO.mk (gl_uniform_f_raw ctx.id u.id 1 x 0.0 0.0 0.0)

pub def Gl.uniform2f (ctx : GlContext) (u : GlUniform) (x : F64) (y : F64) : IO Unit :=
    IO.mk (gl_uniform_f_raw ctx.id u.id 2 x y 0.0 0.0)

pub def Gl.uniform3f (ctx : GlContext) (u : GlUniform) (x : F64) (y : F64) (z : F64) : IO Unit :=
    IO.mk (gl_uniform_f_raw ctx.id u.id 3 x y z 0.0)

pub def Gl.uniform4f (ctx : GlContext) (u : GlUniform) (x : F64) (y : F64) (z : F64) (w : F64) : IO Unit :=
    IO.mk (gl_uniform_f_raw ctx.id u.id 4 x y z w)

/// An integer uniform -- also how a sampler picks its texture unit.
pub def Gl.uniform1i (ctx : GlContext) (u : GlUniform) (x : I64) : IO Unit :=
    state ctx GlState.uniform_i u.id x 0 0

// ─── Buffers, vertex arrays, attributes ──────────────────────────────

pub def Gl.create_buffer (ctx : GlContext) : IO GlBuffer := do {
    let id <- IO.mk (gl_create_raw ctx.id (GlKind.code GlKind.buffer));
    IO.pure { id := id : GlBuffer }
}

pub def Gl.bind_buffer (ctx : GlContext) (target : GlBufferTarget) (b : GlBuffer) : IO Unit :=
    IO.mk (gl_bind_raw ctx.id (GlKind.code GlKind.buffer) (GlBufferTarget.code target) b.id)

pub def Gl.unbind_buffer (ctx : GlContext) (target : GlBufferTarget) : IO Unit :=
    IO.mk (gl_bind_raw ctx.id (GlKind.code GlKind.buffer) (GlBufferTarget.code target) 0)

pub def Gl.delete_buffer (ctx : GlContext) (b : GlBuffer) : IO Unit :=
    IO.mk (gl_delete_raw ctx.id (GlKind.code GlKind.buffer) b.id)

/// A vertex array object, or `none` when the context has none
/// (`has_vertex_arrays`).
pub def Gl.create_vertex_array (ctx : GlContext) : IO (Option GlVertexArray) := do {
    let id <- IO.mk (gl_create_raw ctx.id (GlKind.code GlKind.vertex_array));
    if I64.lt id 1 then IO.pure Option.none else IO.pure (Option.some { id := id : GlVertexArray })
}

pub def Gl.bind_vertex_array (ctx : GlContext) (v : GlVertexArray) : IO Unit :=
    IO.mk (gl_bind_raw ctx.id (GlKind.code GlKind.vertex_array) 0 v.id)

pub def Gl.unbind_vertex_array (ctx : GlContext) : IO Unit :=
    IO.mk (gl_bind_raw ctx.id (GlKind.code GlKind.vertex_array) 0 0)

pub def Gl.delete_vertex_array (ctx : GlContext) (v : GlVertexArray) : IO Unit :=
    IO.mk (gl_delete_raw ctx.id (GlKind.code GlKind.vertex_array) v.id)

/// `vertexAttribPointer` over the bound array buffer; `stride` and
/// `offset` are in bytes.
pub def Gl.vertex_attrib_pointer (ctx : GlContext) (index : I64) (size : I64) (typ : GlAttribType)
    (normalized : Bool) (stride : I64) (offset : I64) : IO Unit :=
    IO.mk (gl_vertex_attrib_raw ctx.id index size (GlAttribType.code typ) (bit normalized 1) stride offset)

pub def Gl.enable_vertex_attrib (ctx : GlContext) (index : I64) : IO Unit :=
    state ctx GlState.attrib_array index 1 0 0

pub def Gl.disable_vertex_attrib (ctx : GlContext) (index : I64) : IO Unit :=
    state ctx GlState.attrib_array index 0 0 0

// ─── State and drawing ───────────────────────────────────────────────

pub def Gl.viewport (ctx : GlContext) (x : I64) (y : I64) (w : I64) (h : I64) : IO Unit :=
    state ctx GlState.viewport x y w h

pub def Gl.clear_color (ctx : GlContext) (r : F64) (g : F64) (b : F64) (a : F64) : IO Unit :=
    IO.mk (gl_clear_color_raw ctx.id r g b a)

pub def Gl.clear (ctx : GlContext) (which : GlClear) : IO Unit :=
    state ctx GlState.clear (GlClear.code which) 0 0 0

pub def Gl.enable (ctx : GlContext) (c : GlCap) : IO Unit :=
    state ctx GlState.cap (GlCap.code c) 1 0 0

pub def Gl.disable (ctx : GlContext) (c : GlCap) : IO Unit :=
    state ctx GlState.cap (GlCap.code c) 0 0 0

pub def Gl.blend_func (ctx : GlContext) (src : GlBlendFactor) (dst : GlBlendFactor) : IO Unit :=
    state ctx GlState.blend_func (GlBlendFactor.code src) (GlBlendFactor.code dst) 0 0

pub def Gl.depth_func (ctx : GlContext) (c : GlCompare) : IO Unit :=
    state ctx GlState.depth_func (GlCompare.code c) 0 0 0

pub def Gl.depth_mask (ctx : GlContext) (write : Bool) : IO Unit :=
    state ctx GlState.depth_mask (bit write 1) 0 0 0

pub def Gl.cull_face (ctx : GlContext) (f : GlFace) : IO Unit :=
    state ctx GlState.cull_face (GlFace.code f) 0 0 0

pub def Gl.front_face (ctx : GlContext) (w : GlWinding) : IO Unit :=
    state ctx GlState.front_face (GlWinding.code w) 0 0 0

/// `drawArrays`: `count` vertices from `first`.
pub def Gl.draw_arrays (ctx : GlContext) (p : GlPrimitive) (first : I64) (count : I64) : IO Unit :=
    IO.mk (gl_draw_raw ctx.id 0 (GlPrimitive.code p) first count)

/// `drawElements` over the bound element buffer, whose indices are 32-bit
/// unsigned (`Buf I32`); `offset` is in bytes.
pub def Gl.draw_elements (ctx : GlContext) (p : GlPrimitive) (count : I64) (offset : I64) : IO Unit :=
    IO.mk (gl_draw_raw ctx.id 1 (GlPrimitive.code p) count offset)

// ─── Textures ────────────────────────────────────────────────────────

pub def Gl.create_texture (ctx : GlContext) : IO GlTexture := do {
    let id <- IO.mk (gl_create_raw ctx.id (GlKind.code GlKind.texture));
    IO.pure { id := id : GlTexture }
}

pub def Gl.bind_texture (ctx : GlContext) (target : GlTextureTarget) (t : GlTexture) : IO Unit :=
    IO.mk (gl_bind_raw ctx.id (GlKind.code GlKind.texture) (GlTextureTarget.code target) t.id)

pub def Gl.delete_texture (ctx : GlContext) (t : GlTexture) : IO Unit :=
    IO.mk (gl_delete_raw ctx.id (GlKind.code GlKind.texture) t.id)

/// Select texture unit `unit` (0 = `TEXTURE0`) for the next bind.
pub def Gl.active_texture (ctx : GlContext) (unit_index : I64) : IO Unit :=
    state ctx GlState.active_texture unit_index 0 0 0

/// Minification and magnification filters for the bound texture.
pub def Gl.tex_filter (ctx : GlContext) (target : GlTextureTarget) (min : GlFilter) (mag : GlFilter)
    : IO Unit := do {
    let t := GlTextureTarget.code target;
    let _ <- state ctx GlState.tex_parameter t 10241 (GlFilter.code min) 0;
    state ctx GlState.tex_parameter t 10240 (GlFilter.code mag) 0
}

/// Wrap modes along s and t for the bound texture.
pub def Gl.tex_wrap (ctx : GlContext) (target : GlTextureTarget) (s : GlWrap) (t : GlWrap) : IO Unit := do {
    let tc := GlTextureTarget.code target;
    let _ <- state ctx GlState.tex_parameter tc 10242 (GlWrap.code s) 0;
    state ctx GlState.tex_parameter tc 10243 (GlWrap.code t) 0
}

pub def Gl.generate_mipmap (ctx : GlContext) (target : GlTextureTarget) : IO Unit :=
    state ctx GlState.generate_mipmap (GlTextureTarget.code target) 0 0 0

/// `UNPACK_FLIP_Y_WEBGL`: flip uploaded images so row 0 is the bottom.
pub def Gl.flip_y (ctx : GlContext) (on : Bool) : IO Unit :=
    state ctx GlState.pixel_store 37440 (bit on 1) 0 0

/// Upload a loaded image into the bound texture as RGBA8. False while the
/// image is still loading or failed (`GlImage.poll`).
pub def Gl.tex_image_from_image (ctx : GlContext) (target : GlTextureTarget) (img : GlImage) : IO Bool := do {
    let ok <- IO.mk (gl_tex_image_from_image_raw ctx.id (GlTextureTarget.code target) img.id);
    IO.pure (I64.beq ok 1)
}

// ─── Images ──────────────────────────────────────────────────────────

/// Start loading `url` (CORS-anonymous, so a cross-origin image needs the
/// server's permission to become a texture). Poll with `GlImage.poll`.
pub def GlImage.load (url : String) : IO GlImage := do {
    let id <- IO.mk (image_load_begin_raw url);
    IO.pure { id := id : GlImage }
}

/// 0 = loading, 1 = ready, 2 = failed (the fetch/clipboard convention).
pub def GlImage.poll (img : GlImage) : IO I64 := IO.mk (image_info_raw img.id 0)

/// The natural size in pixels, (0, 0) until the image is ready.
pub def GlImage.size (img : GlImage) : IO (Pair I64 I64) := do {
    let w <- IO.mk (image_info_raw img.id 1);
    let h <- IO.mk (image_info_raw img.id 2);
    IO.pure (Pair.pair w h)
}
