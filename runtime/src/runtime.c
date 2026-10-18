/* The C runtime linked into every compiled binary.
 *
 * This file is the translation-unit wrapper: the actual code lives in
 * runtime_core.c (portable), runtime_libc.c (formatting that needs libc),
 * and one platform file. The build compiles this path for every target
 * (`Runtime.c_path`); the target selects a platform with
 * `-DMONAD_TARGET_WASI` / `-DMONAD_TARGET_WEB` (`llvm/src/target.mo`).
 *
 * The native argv is unchanged: with no target define this is the same
 * POSIX/Boehm runtime it always was.
 */

#if !defined(MONAD_TARGET_WASI) && !defined(MONAD_TARGET_WEB)
#define MONAD_TARGET_NATIVE 1
/* GC_THREADS must precede <gc.h>, and gc.h must precede every system
   header (see that file's own comment), so this comes before runtime_abi.h
   as well. */
#include "runtime_posix_prelude.h"
#endif

#include "runtime_abi.h"

#ifndef MONAD_TARGET_WEB
#include <string.h>
#endif

#include "runtime_core.c"

#ifndef MONAD_TARGET_WEB
#include "runtime_libc.c"
#endif

#if defined(MONAD_TARGET_NATIVE)
#include "platform_posix.c"
#elif defined(MONAD_TARGET_WASI)
#include "platform_wasi.c"
#else
#include "platform_web.c"
#endif
