/* Win32/mingw-w64 headers for the runtime. The Windows counterpart of
   runtime_posix_prelude.h, and included FIRST for the same reason that file
   gives: Boehm's <gc.h> has to precede the system headers, and it has to see
   the collector configuration before anything else does.

   GC_THREADS IS DELIBERATELY ABSENT, and that is the single most important
   difference from the POSIX prelude. This target has no fibers: the whole
   concurrency surface (fork_io, await/poll/cancel_fiber, scopes, channels) is
   refused by the compiler's own target gate, so every thread that could
   allocate is the one Boehm already knows about, and a single-threaded
   collector is the correct one. Defining GC_THREADS here would ask for
   GC_pthread_create -- which does not exist on this platform -- and would
   make the collector's own registration machinery the only thing that could
   allocate from a second thread.

   WHAT IS MISSING FROM THIS LIST, and why, is the honest summary of what the
   Windows target does not have. <pthread.h> does not exist (mingw ships an
   optional winpthreads, which is not pulled in); there is no <sys/statvfs.h>,
   <sys/utsname.h>, <sys/resource.h>, <termios.h>, <sys/poll.h>, <netdb.h> or
   <sys/inotify.h>; and `uname`/`readlink`/`fork`/`execvp`/`lstat` have no
   equivalent at all. The natives that needed them are the ones the gate
   refuses -- see `windows_os_only_natives` in codegen/src/natives.mo -- and
   this file supplies a real substitute only where one exists (GetEnvironment-
   Variable for getenv, FindFirstFile for opendir, _stat for stat, Sleep for
   nanosleep).

   <stdatomic.h> and `_Thread_local` both work under mingw, which is what lets
   runtime_core.c compile unchanged: its Ref/Cell atomics and its
   cancel-flag thread-local are compiled but never contended here. */
#ifndef MONAD_RUNTIME_WINDOWS_PRELUDE_H
#define MONAD_RUNTIME_WINDOWS_PRELUDE_H

#include <gc.h>

#include <stdatomic.h>
#include <stdint.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <errno.h>
#include <time.h>
#include <limits.h>

/* The Win32 surface. `WIN32_LEAN_AND_MEAN` keeps <winsock.h> (and its
   <windows.h>-wide namespace pollution) out; `NOMINMAX` keeps the min/max
   macros from rewriting any `Min`/`Max` identifier a future edit adds. */
#define WIN32_LEAN_AND_MEAN 1
#ifndef NOMINMAX
#define NOMINMAX 1
#endif
#include <windows.h>
/* `getppid`'s substitute (`sys_int` op 1) walks a process snapshot, which
   lives in the Tool Help library rather than in <windows.h>. */
#include <tlhelp32.h>

/* The POSIX-named CRT subset: _read/_write/_close/_lseeki64, _pipe, _setmode,
   and the _O_* flags. This is the one place the two platforms genuinely
   agree, and using the underscore spellings keeps the C in platform_win32.c
   recognisable against platform_posix.c. */
#include <io.h>
#include <fcntl.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <direct.h>
#include <process.h>

#endif /* MONAD_RUNTIME_WINDOWS_PRELUDE_H */
