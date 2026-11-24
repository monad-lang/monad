/* The C runtime linked into every compiled binary.
 *
 * This file is the translation-unit wrapper: the actual code lives in
 * runtime_core.c (portable), runtime_libc.c (formatting that needs libc),
 * and one platform file. The build compiles this path for every target
 * (`Runtime.c_path`); the target selects a platform with
 * `-DMONAD_TARGET_WASI` / `-DMONAD_TARGET_WEB` / `-DMONAD_TARGET_WINDOWS`
 * (`llvm/src/target.mo`).
 *
 * The native argv is unchanged: with no target define this is the same
 * POSIX/Boehm runtime it always was. `MONAD_TARGET_WINDOWS` is set by a
 * mingw cc and is what selects platform_win32.c.
 */

#if !defined(MONAD_TARGET_WASI) && !defined(MONAD_TARGET_WEB) && !defined(MONAD_TARGET_WINDOWS)
#define MONAD_TARGET_NATIVE 1
/* GC_THREADS must precede <gc.h>, and gc.h must precede every system
   header (see that file's own comment), so this comes before runtime_abi.h
   as well. */
#include "runtime_posix_prelude.h"
#endif

#if defined(MONAD_TARGET_WINDOWS)
/* The same ordering rule with a different prelude: Win32 in place of
   pthreads/POSIX, and GC_THREADS deliberately absent because this target
   has no fibers (see runtime_windows_prelude.h). */
#include "runtime_windows_prelude.h"
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
#elif defined(MONAD_TARGET_WINDOWS)
#include "platform_win32.c"
#else
#include "platform_web.c"
#endif
