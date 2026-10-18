/* POSIX/native headers for the runtime. Included FIRST: GC_THREADS must
   precede <gc.h>, and gc.h must precede the system headers (see its own
   comment in runtime.c history). */
/* THREADED Boehm, and this define has to come BEFORE <gc.h>: the header
   uses it to decide whether it declares the thread API at all, and
   (gc/gc_pthread_redirects.h) to redirect pthread_create/pthread_join to
   GC_pthread_create/GC_pthread_join -- which is what registers a new
   thread with the collector and hands it the right stack base. Without
   it, a worker thread that allocates makes the collector corrupt itself
   silently: Boehm's single-threaded mode assumes only the GC_INIT thread
   ever allocates. nixpkgs' boehmgc IS built with thread support --
   GC_pthread_create and GC_register_my_thread are defined symbols in its
   libgc.so, verified with nm(1) rather than assumed.

   gc.h is also deliberately the FIRST include, as it already was: when
   GC_PTHREADS is on, gc_config_macros.h defines `_REENTRANT` itself with
   a comment saying that only works for system headers included after it.
   `-pthread` on the compile command (llvm/src/link.mo) sets it up front
   as well, which is the belt to this braces. */
#define GC_THREADS
#include <gc.h>
#include <pthread.h>
#include <errno.h>
#include <stdatomic.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <sys/stat.h>
#include <dirent.h>
#include <sys/resource.h>
#include <sys/wait.h>
#include <signal.h>
#include <sys/socket.h>
#include <netinet/in.h>
#include <netdb.h>
#include <unistd.h>
#include <fcntl.h>
#include <termios.h>
#include <sys/ioctl.h>
#include <poll.h>
#include <limits.h>

