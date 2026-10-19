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

def EnvReport.opt_path (o : Option Path) : String :=
    match o {
        Option.some p => Path.to_string p,
        Option.none => "(none)",
    }

def EnvReport.yesno (b : Bool) : String :=
    if b then "yes" else "no"

def EnvReport.tool_line (e : Doctor.Env) : String :=
    "tools:          llc=" ++ EnvReport.yesno e.tools.llc
        ++ ", clang=" ++ EnvReport.yesno e.tools.clang
        ++ ", pkg-config=" ++ EnvReport.yesno e.tools.pkg_config
        ++ ", bdw-gc=" ++ EnvReport.yesno e.tools.bdw_gc

def EnvReport.origin_of (uname : String) : String :=
    "(from uname -sm, " ++ uname ++ ")"

pub def EnvReport.run : IO I64 := do {
    let e <- Doctor.gather true;
    let origin_text : String := EnvReport.origin_of e.platform.uname_sm;
    let origin : String :=
        if String.is_empty e.platform.uname_sm
        then "(uname -sm failed)"
        else origin_text;
    IO.println ("platform:       " ++ e.platform.platform ++ "   " ++ origin);
    if e.platform.used_fallback then IO.println ("                " ++ e.platform.note) else return unit;
    IO.println ("home:           " ++ Path.to_string e.home.path ++ "  (" ++ e.home.source ++ ")");
    IO.println ("active:         " ++ EnvReport.opt e.active);
    let root : Option Path :=
        match e.active {
            Option.some tag =>
                match Layout.tag_path tag {
                    Result.ok tag_path => Option.some (Layout.version_dir e.home tag_path),
                    Result.err _ => Option.none,
                },
            Option.none => Option.none,
        };
    IO.println ("toolchain root: " ++ EnvReport.opt_path root ++ " (sources present: " ++ I64.to_string (List.length e.sources) ++ ")");
    IO.println ("PATH:           " ++ Path.to_string (Layout.bin_dir e.home) ++ " (" ++ (if e.path_has_bin then "present" else "absent") ++ ")");
    IO.println ("compiler:       " ++ EnvReport.opt_path e.monad_link);
    IO.println (EnvReport.tool_line e);
    let overrides : String :=
        if List.is_empty e.overrides then "(none)"
        else Doctor.join_names (Doctor.override_names e.overrides);
    IO.println ("overrides:      " ++ overrides);
    return 0
}
