// trellis_ui's library root: the graph model and wire codec, the fuzzy
// search and the projection to an `oak_ui` graph spec. All pure; the native
// `trellis` tool writes graphs with the same codec the browser reads.

pub use lib::seq {Seq.fold, Seq.reverse, Seq.map, Seq.filter, Seq.length, Seq.any, Seq.find, Seq.append, Seq.lines}

pub use lib::smap {Smap.empty, Smap.insert, Smap.get, Smap.has, Smap.get_i64, Smap.get_str}

pub use lib::model {
    Trellis.ModuleNode, Trellis.DeclNode, Trellis.Edge, Trellis.Graph,
    Trellis.Graph.empty, Trellis.Graph.encode, Trellis.Graph.decode,
    Trellis.decl_id, Trellis.parse_nat, Trellis.DeclNode.is_proof, Trellis.DeclNode.is_test,
    Trellis.escape_field, Trellis.unescape_field,
}

pub use lib::docs {Trellis.render_docs}

pub use lib::signature {Trellis.sig_targets, Trellis.sig_view}

pub use lib::fuzzy {Fuzzy.Hit, Fuzzy.score, Fuzzy.search, Fuzzy.motes}

pub use lib::project {
    Trellis.Level, Trellis.Grouping, Trellis.Direction, Trellis.Settings, Trellis.Settings.initial,
    Trellis.Level.slug, Trellis.Level.of_slug, Trellis.Grouping.slug, Trellis.Grouping.of_slug,
    Trellis.Direction.slug, Trellis.Direction.of_slug,
    Trellis.Projection, Trellis.Section, Trellis.Drawn, Trellis.Prepared, Trellis.Prepared.empty,
    Trellis.prepare, Trellis.cut, Trellis.pack_size, Trellis.key_at, Trellis.effective_grouping, Trellis.project,
    Trellis.neighbours, Trellis.find_decl, Trellis.find_module, Trellis.lift_key,
}

pub use lib::app {
    Trellis.Model, Trellis.Msg, Trellis.Effect, Trellis.Model.initial, Trellis.update, Trellis.view,
    Trellis.subscriptions, Trellis.program, Trellis.refresh, Trellis.pick, Trellis.selected_key, Trellis.css,
    Trellis.source_url,
}
