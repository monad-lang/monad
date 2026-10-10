/// `ToolRegistry` -- split from `tool.mo` for the same reason
/// `message_types.mo` is split from `message.mo`: a top-level function
/// in the same file as a `reflect_type_info!` invocation (`tool.mo`
/// derives `ToolSpec`) that references one of this file's own
/// constructors fails macro-expansion's capture pass with `unbound
/// variable`, even though the constructor is real.
use shuttle::tool {ToolSpec, ToolImpl}
use std::map {}

pub type ToolRegistry {
    registry (tools : BTreeMap String ToolImpl),
}

pub def ToolRegistry.empty : ToolRegistry := ToolRegistry.registry BTreeMap.empty

pub def ToolRegistry.register (impl : ToolImpl) (reg : ToolRegistry) : ToolRegistry :=
    match reg {
        ToolRegistry.registry tools =>
            match impl { mk spec run => ToolRegistry.registry (Map.insert spec.name impl tools) }
    }

pub def ToolRegistry.lookup (name : String) (reg : ToolRegistry) : Option ToolImpl :=
    match reg {
        ToolRegistry.registry tools => Map.lookup name tools
    }

pub def ToolRegistry.specs (reg : ToolRegistry) : List ToolSpec :=
    match reg {
        ToolRegistry.registry tools => List.map pair_to_spec (BTreeMap.to_list tools)
    }

def pair_to_spec (p : Pair String ToolImpl) : ToolSpec :=
    match p {
        Pair.pair name impl => match impl { mk spec run => spec }
    }
