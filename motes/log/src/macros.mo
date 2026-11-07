/// The level macros: `info! log "built {n} files in {ms}ms"` formats its
/// template with `fmt!` (`init/src/format.mo`) and logs it at that level.
/// Import them from this module (`use log::macros {info}`): the `log` hub's
/// re-exports are not declarations, so `use log {info}` cannot name them.
///
/// The template is formatted before the level check, so its holes are
/// evaluated even for a line the logger drops; keep costly holes behind
/// `Logger.should_emit`.
use init::format {fmt}
use log::logger {Logger, Logger.trace, Logger.debug, Logger.info, Logger.warn, Logger.error}

#[at term]
#[returns expr]
defmacro trace logger template := quote {
    Logger.trace logger (fmt! template)
}

#[at term]
#[returns expr]
defmacro debug logger template := quote {
    Logger.debug logger (fmt! template)
}

#[at term]
#[returns expr]
defmacro info logger template := quote {
    Logger.info logger (fmt! template)
}

#[at term]
#[returns expr]
defmacro warn logger template := quote {
    Logger.warn logger (fmt! template)
}

#[at term]
#[returns expr]
defmacro error logger template := quote {
    Logger.error logger (fmt! template)
}
