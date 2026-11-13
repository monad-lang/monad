// Texture state and two-phase image loading, without Oak.
//
// `main` mounts a canvas, makes a texture, sets its filter/wrap/flip state
// and starts loading two images (one that will fail). The loads finish only
// when the harness says so, so `probe` -- an export the harness calls after
// that -- polls both, uploads the ready one and reports in `span#report`.
// `wasm/web/webgl_texture_smoke.mjs` drives it over `stub_gl.mjs`.
#![mote { name := "webgl_texture", deps := [web_wasm] }]

use web_wasm::dom {Dom.append, Dom.create, Dom.query, Dom.root, Dom.set_attr, Dom.text_node}
use web_wasm::gl {
    GlContext, GlImage, GlTexture, GlTextureTarget, GlFilter, GlWrap, GlOptions.default,
    Gl.context, Gl.create_texture, Gl.bind_texture, Gl.active_texture, Gl.tex_filter,
    Gl.tex_wrap, Gl.flip_y, Gl.generate_mipmap, Gl.tex_image_from_image, GlImage.load,
    GlImage.poll, GlImage.size,
}

def report (text : String) : IO Unit := do {
    let root <- Dom.root;
    let span <- Dom.create "span";
    let _ <- Dom.set_attr span "id" "report";
    let t <- Dom.text_node text;
    let _ <- Dom.append span t;
    Dom.append root span
}

def prepare (ctx : GlContext) : IO Unit := do {
    let tex <- Gl.create_texture ctx;
    let _ <- Gl.active_texture ctx 0;
    let _ <- Gl.bind_texture ctx GlTextureTarget.texture_2d tex;
    let _ <- Gl.tex_filter ctx GlTextureTarget.texture_2d GlFilter.linear_mipmap_linear GlFilter.linear;
    let _ <- Gl.tex_wrap ctx GlTextureTarget.texture_2d GlWrap.clamp_to_edge GlWrap.repeat;
    let _ <- Gl.flip_y ctx true;
    let ok <- GlImage.load "board.png";
    let bad <- GlImage.load "missing.png";
    let p1 <- GlImage.poll ok;
    let p2 <- GlImage.poll bad;
    let early <- Gl.tex_image_from_image ctx GlTextureTarget.texture_2d ok;
    report (String.concat_list [
        "polls=", I64.to_string p1, ",", I64.to_string p2,
        " early=", if early then "yes" else "no",
    ])
}

def main : IO Unit := do {
    let root <- Dom.root;
    let canvas <- Dom.create "canvas";
    let _ <- Dom.append root canvas;
    let found <- Gl.context canvas GlOptions.default;
    match found {
        Option.none => report "no webgl",
        Option.some ctx => prepare ctx,
    }
}

def finish (ctx : GlContext) : IO Unit := do {
    // Ids are deterministic in a fresh page: images 1 and 2 in load order.
    let ok : GlImage := { id := 1 };
    let bad : GlImage := { id := 2 };
    let p1 <- GlImage.poll ok;
    let p2 <- GlImage.poll bad;
    let size <- GlImage.size ok;
    let uploaded <- Gl.tex_image_from_image ctx GlTextureTarget.texture_2d ok;
    let failed_upload <- Gl.tex_image_from_image ctx GlTextureTarget.texture_2d bad;
    let _ <- Gl.generate_mipmap ctx GlTextureTarget.texture_2d;
    let dims : String :=
        match size { Pair.pair w h => String.concat_list [I64.to_string w, "x", I64.to_string h] };
    report (String.concat_list [
        "polls=", I64.to_string p1, ",", I64.to_string p2, " size=", dims,
        " uploaded=", if uploaded then "yes" else "no",
        " failed_upload=", if failed_upload then "yes" else "no",
    ])
}

#[export "c"]
def probe : IO Unit := do {
    let canvas <- Dom.query "canvas";
    let found <- Gl.context canvas GlOptions.default;
    match found {
        Option.none => report "no webgl",
        Option.some ctx => finish ctx,
    }
}
