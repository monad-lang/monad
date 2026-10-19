use std::list {List.length}
/// `monadup env`: the resolved environment, in the spirit of `rustup show`.
use lib::doctor {*}
use lib::layout {*}
use lib::text {*}

def EnvReport.opt (o : Option String) : String :=
    match o {
        Option.some s => s,
        Option.none => "(none)",
    }

def EnvReport.yesno (b : Bool) : String :=
    if b then "yes" else "no"

def EnvReport.tool_line (e : Doctor.Env) : String :=
    String.concat "tools:          llc=" (String.concat (EnvReport.yesno e.tools.llc)
        (String.concat ", clang=" (String.concat (EnvReport.yesno e.tools.clang)
            (String.concat ", pkg-config=" (String.concat (EnvReport.yesno e.tools.pkg_config)
                (String.concat ", bdw-gc=" (EnvReport.yesno e.tools.bdw_gc)))))))

def EnvReport.origin_of (uname : String) : String :=
    String.concat "(from uname -sm, " (String.concat uname ")")

pub def EnvReport.run : IO I64 := do {
    let e <- Doctor.gather true;
    let origin_text : String := EnvReport.origin_of e.platform.uname_sm;
    let origin : String :=
        if String.is_empty e.platform.uname_sm
        then "(uname -sm failed)"
        else origin_text;
    IO.println (String.concat "platform:       " (String.concat e.platform.platform
        (String.concat "   " origin)));
    if e.platform.used_fallback then IO.println (String.concat "                " e.platform.note) else return unit;
    IO.println (String.concat "home:           " (String.concat e.home.path
        (String.concat "  (" (String.concat e.home.source ")"))));
    IO.println (String.concat "active:         " (EnvReport.opt e.active));
    let root : String :=
        match e.active {
            Option.some tag => Layout.version_dir e.home tag,
            Option.none => "(none)",
        };
    IO.println (String.concat "toolchain root: " (String.concat root
        (String.concat " (sources present: " (String.concat (I64.to_string (List.length e.sources)) ")"))));
    IO.println (String.concat "PATH:           " (String.concat (Layout.bin_dir e.home)
        (String.concat " (" (String.concat (if e.path_has_bin then "present" else "absent") ")"))));
    IO.println (String.concat "compiler:       " (EnvReport.opt e.monad_link));
    IO.println (EnvReport.tool_line e);
    let overrides : String :=
        if List.is_empty e.overrides then "(none)"
        else Doctor.join_names (Doctor.override_names e.overrides);
    IO.println (String.concat "overrides:      " overrides);
    return 0
}
