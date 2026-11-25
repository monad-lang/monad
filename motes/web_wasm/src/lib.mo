// web_wasm's library root -- bare `use web_wasm` resolves here.
//
// The browser platform boundary: opaque handles, the ABI spec, the
// generated loader, and the thin IO wrappers over the RawIO externs.
// Nothing outside this mote declares a web extern.

pub use lib::types {Node, RequestId, ClipboardOp, CryptoOp, WebKey, RtcPeer, MediaStream, MediaStreamOp}
pub use web_event::event {WebEvent, FileInfo}

pub use lib::web_abi {
    WebAbi, WebAbi.default, WebExport, WebImport,
}

pub use lib::glue {Glue.loader}
pub use lib::shell {ShellOptions, Shell.default_options, Shell.index_html}

pub use lib::dom {
    Dom.create, Dom.create_svg, Dom.in_svg, Dom.text_node, Dom.comment, Dom.root, Dom.append, Dom.insert_before,
    Dom.remove, Dom.replace, Dom.set_attr, Dom.remove_attr, Dom.set_text,
    Dom.on, Dom.on_with, Dom.on_window, Dom.off_window, Dom.on_document,
    Dom.off_document, Dom.on_frame, Dom.off_frame, Dom.child, Dom.child_count,
    Dom.node_type, Dom.tag_name, Dom.value, Dom.query,
    Dom.element_at, Dom.attr, Dom.focus,
}

pub use lib::fetch {
    Fetch.begin, Fetch.begin_with, Fetch.poll, Fetch.status,
    Fetch.response_headers, Fetch.read, decode_headers,
}
pub use lib::clipboard {
    Clipboard.available, Clipboard.read_begin, Clipboard.write_begin,
    Clipboard.poll, Clipboard.read, Clipboard.error,
    Clipboard.read_result, Clipboard.write_result,
}
pub use lib::event {
    WebEvent.current, WebEvent.prevent_default, WebEvent.stop_propagation, WebEvent.split_lines,
}
pub use lib::clock {Clock.now_ms, Clock.monotonic_ms}
pub use lib::storage {
    Storage.has, Storage.get_raw, Storage.get, Storage.set,
    Storage.remove, Storage.clear,
}
pub use lib::media {Media.matches, Media.watch, Media.unwatch}
pub use lib::crypto {
    Crypto.random_bytes, Crypto.sha256_begin, Crypto.poll, Crypto.result_hex,
    Crypto.error, Crypto.op_key, Crypto.await_op,
    WebCrypto.generate_key_begin, WebCrypto.export_public_jwk_begin,
    WebCrypto.export_public_raw_begin, WebCrypto.sign_begin,
}
pub use lib::keystore {
    KeyStore.empty_state, KeyStore.put_begin, KeyStore.get_begin,
    KeyStore.delete_begin, KeyStore.get,
}
pub use lib::window {
    Window.origin, Window.href, Window.pathname, Window.search,
    Window.search_param, Window.reload, Window.navigate, Window.replace,
}
pub use lib::memory {Memory.heap_bytes, Memory.heap_used}
pub use lib::timer {Timer.base, Timer.is_id, Timer.after}
pub use lib::random {WebRandom, WebRandom.new, SplitMix64.seed_from_clock}
pub use lib::splitmix {
    SplitMix64, SplitMix64.seed, SplitMix64.next, SplitMix64.below,
}
pub use lib::console {Console.log}
pub use lib::try_bridge {TryBridge.push_result}
pub use lib::worker {Worker.run, Worker.poll, Worker.status, Worker.value, Worker.typ, Worker.error, Worker.notes, Worker.cancel}
pub use lib::keep {Keep.save, Keep.load}
pub use lib::canvas {Canvas.client_size, Canvas.buffer_size, Canvas.fit, Canvas.pixel_ratio}
pub use lib::gl {
    GlContext, GlShader, GlProgram, GlBuffer, GlTexture, GlVertexArray, GlUniform, GlImage,
    GlFramebuffer, GlAttachment, Gl.create_framebuffer, Gl.bind_framebuffer,
    Gl.bind_default_framebuffer, Gl.delete_framebuffer, Gl.has_depth_texture,
    Gl.tex_image_depth, Gl.framebuffer_texture, Gl.framebuffer_complete, Gl.color_mask,
    Gl.polygon_offset,
    GlOptions, GlOptions.default, GlOptions.flags, GlShaderStage, GlBufferTarget,
    GlTextureTarget, GlUsage, GlPrimitive, GlCap, GlBlendFactor, GlCompare, GlFace,
    GlWinding, GlAttribType, GlFilter, GlWrap, GlClear,
    Gl.context, Gl.version, Gl.is_lost, Gl.drawing_buffer_size, Gl.error,
    Gl.has_vertex_arrays, Gl.compile_shader, Gl.link_program, Gl.program,
    Gl.use_program, Gl.delete_program, Gl.delete_shader, Gl.attrib_location,
    Gl.uniform_location, Gl.uniform1f, Gl.uniform2f, Gl.uniform3f, Gl.uniform4f,
    Gl.uniform1i, Gl.create_buffer, Gl.bind_buffer, Gl.unbind_buffer, Gl.delete_buffer,
    Gl.create_vertex_array, Gl.bind_vertex_array, Gl.unbind_vertex_array,
    Gl.delete_vertex_array, Gl.vertex_attrib_pointer, Gl.enable_vertex_attrib,
    Gl.disable_vertex_attrib, Gl.viewport, Gl.clear_color, Gl.clear, Gl.enable,
    Gl.disable, Gl.blend_func, Gl.depth_func, Gl.depth_mask, Gl.cull_face,
    Gl.front_face, Gl.draw_arrays, Gl.draw_elements, Gl.create_texture,
    Gl.bind_texture, Gl.delete_texture, Gl.active_texture, Gl.tex_filter, Gl.tex_wrap,
    Gl.generate_mipmap, Gl.flip_y, Gl.tex_image_from_image, GlImage.load,
    GlImage.poll, GlImage.size, Gl.has_uint_indices, Gl.buffer_data_f32, Gl.buffer_data_i32,
    Gl.buffer_sub_data_f32, Gl.uniform_matrix4, Gl.tex_image_rgba, Gl.f32_buf, Gl.i32_buf,
    Gl.u8_buf,
}

pub use lib::websocket {
    WebSocket.connect, WebSocket.state, WebSocket.close, WebSocket.free, WebSocket.send,
    WebSocket.send_bytes, WebSocket.next, WebSocket.drain, WebSocket.pending,
    WebSocket.watch, WebSocket.unwatch,
}

pub use lib::rtc {
    Rtc.connect, Rtc.state, Rtc.free, Rtc.set_local, Rtc.set_remote, Rtc.add_ice,
    Rtc.create_data_channel, Rtc.send, Rtc.send_bytes, Rtc.close, Rtc.add_stream,
    Rtc.next, Rtc.drain, Rtc.watch, Rtc.unwatch,
}
pub use lib::media_stream {
    MediaStream.get_user_media_begin, MediaStream.get_display_media_begin,
    MediaStream.request_av, MediaStream.request_video,
    MediaStream.request_audio, MediaStream.request_display,
    MediaStream.poll, MediaStream.result, MediaStream.error, MediaStream.await,
    MediaStream.attach, MediaStream.stop, MediaStream.release,
}
