/* A conservative, non-moving mark-sweep heap for wasm32 linear memory.
 *
 * Included by platform_web.c (needs memset and the Header layout from
 * runtime_core.c). Wasm locals are invisible to a scan, so a collection is
 * only sound when no Monad frame is live: `monad_export_leave` runs it when
 * the export depth returns to 0, rooting the export's result. Roots are the
 * data segment + .bss (minus this file's own state), the live shadow stack
 * and the caller's extra words.
 *
 * Layout: the heap is a run of 64 KiB wasm pages from `gc.heap_start`. A
 * SMALL page holds one size class; its first GC_SMALL_HDR bytes are the
 * page's `allocated`/`marked`/`noscan` bitmaps. A LARGE object is a run of
 * whole pages (HEAD + CONT). The page table sits in its own grown region
 * below the heap, so it is neither a root nor heap.
 */

#define GC_PAGE 65536u
#define GC_MAX_PAGES 65536u            /* 4 GiB of wasm32 memory */
#define GC_MIN_OBJ 16u
#define GC_BITMAP_BYTES ((GC_PAGE / GC_MIN_OBJ) / 8u)   /* 512 */
#define GC_SMALL_HDR (3u * GC_BITMAP_BYTES)           /* 1536 */
#define GC_SMALL_USABLE (GC_PAGE - GC_SMALL_HDR)

enum { GC_FREE = 0, GC_SMALL = 1, GC_LARGE_HEAD = 2, GC_LARGE_CONT = 3 };
enum { GC_L_ALLOC = 1, GC_L_MARK = 2, GC_L_NOSCAN = 4 };

typedef struct {
    uint8_t kind;
    uint8_t cls;           /* SMALL: size-class index */
    uint8_t lflags;        /* LARGE_HEAD: GC_L_* */
    uint8_t listed;        /* SMALL: on its class's partial list */
    uint32_t n;            /* HEAD: page count; CONT: distance to the head */
    uint32_t next_partial; /* SMALL: next page with a free slot, +1 (0 = end) */
    uint16_t cursor;       /* SMALL: first slot worth probing */
    uint16_t live;         /* SMALL: allocated slots */
} GcPage;

static const uint32_t gc_classes[] = {
    16, 32, 48, 64, 80, 96, 112, 128, 160, 192, 224, 256, 320, 384, 448,
    512, 640, 768, 896, 1024, 1280, 1536, 1792, 2048, 2560, 3072, 3584,
    4096, 5120, 6144, 7168, 8192, 10576, 12688, 15872, 21152, 31744,
};
#define GC_NCLASSES ((int)(sizeof(gc_classes) / sizeof(gc_classes[0])))
#define GC_SMALL_MAX 31744u

#define GC_MARK_STACK 65536

/* Everything the collector owns that is not a root lives in this one
   struct, which the data-segment scan skips. */
static struct {
    int inited;
    int depth;             /* live export/main frames */
    GcPage* pages;         /* GC_MAX_PAGES entries */
    uint64_t heap_start;   /* page aligned */
    uint32_t npages;       /* heap pages in use (grown) */
    uint32_t free_pages;
    uint32_t rover;
    uint32_t partial[GC_NCLASSES]; /* page index + 1, 0 = none */
    uint64_t live_bytes;   /* after the last sweep */
    uint64_t since_gc;     /* bytes allocated since the last sweep */
    int64_t collections;
    int overflow;
    uint32_t msp;
    uint32_t mark_stack[GC_MARK_STACK];
} gc;

extern unsigned char __heap_base;
extern unsigned char __global_base;
extern unsigned char __data_end;
extern unsigned char __stack_high;

static void web_oom(uint64_t want, uint64_t have);

/* ── page bookkeeping ───────────────────────────────────────────────── */

static uint8_t* gc_page_addr(uint32_t i) {
    return (uint8_t*)(uintptr_t)(gc.heap_start + (uint64_t)i * GC_PAGE);
}

static uint8_t* gc_bm_alloc(uint32_t i) { return gc_page_addr(i); }
static uint8_t* gc_bm_mark(uint32_t i) { return gc_page_addr(i) + GC_BITMAP_BYTES; }
static uint8_t* gc_bm_noscan(uint32_t i) { return gc_page_addr(i) + 2u * GC_BITMAP_BYTES; }

static int gc_bit(const uint8_t* bm, uint32_t k) { return (bm[k >> 3] >> (k & 7)) & 1; }
static void gc_set(uint8_t* bm, uint32_t k) { bm[k >> 3] |= (uint8_t)(1u << (k & 7)); }
static void gc_clr(uint8_t* bm, uint32_t k) { bm[k >> 3] &= (uint8_t)~(1u << (k & 7)); }

static uint32_t gc_slots(int cls) { return GC_SMALL_USABLE / gc_classes[cls]; }

static void gc_init(void) {
    if (gc.inited) return;
    gc.inited = 1;
    uint64_t base = ((uint64_t)(uintptr_t)&__heap_base + GC_PAGE - 1) & ~(uint64_t)(GC_PAGE - 1);
    uint64_t table = (uint64_t)GC_MAX_PAGES * sizeof(GcPage);
    uint64_t start = (base + table + GC_PAGE - 1) & ~(uint64_t)(GC_PAGE - 1);
    uint64_t have = (uint64_t)__builtin_wasm_memory_size(0) * GC_PAGE;
    if (start > have) {
        if (__builtin_wasm_memory_grow(0, (size_t)((start - have) / GC_PAGE)) == (size_t)-1)
            web_oom(start, have);
    }
    gc.pages = (GcPage*)(uintptr_t)base;
    memset(gc.pages, 0, (size_t)table);
    gc.heap_start = start;
}

/* Claims `n` consecutive FREE pages, growing linear memory when no run
   exists. Returns the first page index. */
static uint32_t gc_take_pages(uint32_t n) {
    if (gc.free_pages >= n) {
        uint32_t run = 0;
        for (uint32_t step = 0; step < gc.npages; step++) {
            uint32_t i = gc.rover + step;
            if (i >= gc.npages) i -= gc.npages;
            if (i == 0) run = 0;   /* a run never wraps */
            if (gc.pages[i].kind == GC_FREE) {
                run++;
                if (run == n) {
                    uint32_t first = i + 1 - n;
                    gc.rover = i + 1 < gc.npages ? i + 1 : 0;
                    gc.free_pages -= n;
                    return first;
                }
            } else {
                run = 0;
            }
        }
    }
    /* Grow at the end; a trailing free run is reused as part of it. */
    uint32_t tail = 0;
    while (tail < gc.npages && tail < n && gc.pages[gc.npages - 1 - tail].kind == GC_FREE) tail++;
    uint32_t need = n - tail;
    if ((uint64_t)gc.npages + need > GC_MAX_PAGES)
        web_oom((uint64_t)n * GC_PAGE, (uint64_t)gc.npages * GC_PAGE);
    uint64_t end = gc.heap_start + ((uint64_t)gc.npages + need) * GC_PAGE;
    uint64_t have = (uint64_t)__builtin_wasm_memory_size(0) * GC_PAGE;
    if (end > have) {
        if (__builtin_wasm_memory_grow(0, (size_t)((end - have) / GC_PAGE)) == (size_t)-1)
            web_oom(end, have);
    }
    uint32_t first = gc.npages - tail;
    gc.free_pages -= tail;
    gc.npages += need;
    return first;
}

static void gc_release_pages(uint32_t first, uint32_t n) {
    for (uint32_t k = 0; k < n; k++) {
        GcPage* p = &gc.pages[first + k];
        memset(p, 0, sizeof(GcPage));
    }
    gc.free_pages += n;
}

/* ── allocation ─────────────────────────────────────────────────────── */

static int gc_class_of(uint32_t size) {
    int lo = 0, hi = GC_NCLASSES - 1;
    while (lo < hi) {
        int mid = (lo + hi) / 2;
        if (gc_classes[mid] >= size) hi = mid; else lo = mid + 1;
    }
    return lo;
}

static void* gc_alloc_small(int cls, int noscan) {
    uint32_t size = gc_classes[cls];
    for (;;) {
        uint32_t pi1 = gc.partial[cls];
        if (!pi1) {
            uint32_t i = gc_take_pages(1);
            GcPage* p = &gc.pages[i];
            p->kind = GC_SMALL;
            p->cls = (uint8_t)cls;
            p->cursor = 0;
            p->live = 0;
            p->next_partial = 0;
            p->listed = 1;
            memset(gc_page_addr(i), 0, GC_SMALL_HDR);
            gc.partial[cls] = i + 1;
            continue;
        }
        uint32_t i = pi1 - 1;
        GcPage* p = &gc.pages[i];
        uint32_t slots = gc_slots(cls);
        uint8_t* am = gc_bm_alloc(i);
        for (uint32_t k = p->cursor; k < slots; k++) {
            if (!gc_bit(am, k)) {
                gc_set(am, k);
                if (noscan) gc_set(gc_bm_noscan(i), k); else gc_clr(gc_bm_noscan(i), k);
                p->cursor = (uint16_t)(k + 1);
                p->live++;
                uint8_t* obj = gc_page_addr(i) + GC_SMALL_HDR + k * size;
                memset(obj, 0, size);
                return obj;
            }
        }
        /* Full: unlink and try the next partial page. */
        gc.partial[cls] = p->next_partial;
        p->next_partial = 0;
        p->listed = 0;
        p->cursor = (uint16_t)slots;
    }
}

static void* gc_alloc_large(uint64_t size, int noscan) {
    uint64_t n64 = (size + GC_PAGE - 1) / GC_PAGE;
    if (n64 > GC_MAX_PAGES) web_oom(size, (uint64_t)gc.npages * GC_PAGE);
    uint32_t n = (uint32_t)n64;
    uint32_t first = gc_take_pages(n);
    gc.pages[first].kind = GC_LARGE_HEAD;
    gc.pages[first].n = n;
    gc.pages[first].lflags = (uint8_t)(GC_L_ALLOC | (noscan ? GC_L_NOSCAN : 0));
    for (uint32_t k = 1; k < n; k++) {
        gc.pages[first + k].kind = GC_LARGE_CONT;
        gc.pages[first + k].n = k;
    }
    uint8_t* obj = gc_page_addr(first);
    memset(obj, 0, (size_t)size);
    return obj;
}

/* A zeroed block of at least `size` bytes; `noscan` blocks are never
   traced (strings, Buf payloads). */
static void* gc_alloc(uint64_t size, int noscan) {
    gc_init();
    if (size == 0) size = 1;
    if (size <= GC_SMALL_MAX) {
        int cls = gc_class_of((uint32_t)size);
        gc.since_gc += gc_classes[cls];
        return gc_alloc_small(cls, noscan);
    }
    uint64_t rounded = (size + GC_PAGE - 1) & ~(uint64_t)(GC_PAGE - 1);
    gc.since_gc += rounded;
    return gc_alloc_large(size, noscan);
}

/* ── pointer resolution ─────────────────────────────────────────────── */

/* The start of the allocated block containing `v`, or 0. Sets *page, *slot
   (slot is ~0u for a large object). */
static uint8_t* gc_resolve(uint64_t v, uint32_t* page, uint32_t* slot) {
    if (v < gc.heap_start) return 0;
    uint64_t off = v - gc.heap_start;
    uint64_t i64 = off / GC_PAGE;
    if (i64 >= gc.npages) return 0;
    uint32_t i = (uint32_t)i64;
    GcPage* p = &gc.pages[i];
    switch (p->kind) {
    case GC_SMALL: {
        uint32_t in = (uint32_t)(off - (uint64_t)i * GC_PAGE);
        if (in < GC_SMALL_HDR) return 0;
        uint32_t size = gc_classes[p->cls];
        uint32_t k = (in - GC_SMALL_HDR) / size;
        if (k >= gc_slots(p->cls) || !gc_bit(gc_bm_alloc(i), k)) return 0;
        *page = i;
        *slot = k;
        return gc_page_addr(i) + GC_SMALL_HDR + k * size;
    }
    case GC_LARGE_CONT:
        i -= p->n;
        p = &gc.pages[i];
        /* fallthrough */
    case GC_LARGE_HEAD:
        if (!(p->lflags & GC_L_ALLOC)) return 0;
        *page = i;
        *slot = ~0u;
        return gc_page_addr(i);
    default:
        return 0;
    }
}

/* ── mark ───────────────────────────────────────────────────────────── */

static void gc_push(uint32_t addr) {
    if (gc.msp < GC_MARK_STACK) gc.mark_stack[gc.msp++] = addr;
    else gc.overflow = 1;
}

static void gc_mark_word(uint64_t v) {
    uint32_t page, slot;
    uint8_t* obj = gc_resolve(v, &page, &slot);
    if (!obj) return;
    if (slot == ~0u) {
        GcPage* p = &gc.pages[page];
        if (p->lflags & GC_L_MARK) return;
        p->lflags |= GC_L_MARK;
        if (!(p->lflags & GC_L_NOSCAN)) gc_push((uint32_t)(uintptr_t)obj);
    } else {
        uint8_t* mm = gc_bm_mark(page);
        if (gc_bit(mm, slot)) return;
        gc_set(mm, slot);
        if (!gc_bit(gc_bm_noscan(page), slot)) gc_push((uint32_t)(uintptr_t)obj);
    }
}

static void gc_scan_range(const uint8_t* lo, const uint8_t* hi) {
    uintptr_t a = ((uintptr_t)lo + 3u) & ~(uintptr_t)3u;
    for (; a + 4 <= (uintptr_t)hi; a += 4) {
        gc_mark_word(*(const uint32_t*)a);
    }
}

static uint64_t gc_obj_size(uint8_t* obj) {
    uint32_t page, slot;
    if (!gc_resolve((uint64_t)(uintptr_t)obj, &page, &slot)) return 0;
    if (slot == ~0u) return (uint64_t)gc.pages[page].n * GC_PAGE;
    return gc_classes[gc.pages[page].cls];
}

static void gc_drain(void) {
    while (gc.msp) {
        uint8_t* obj = (uint8_t*)(uintptr_t)gc.mark_stack[--gc.msp];
        gc_scan_range(obj, obj + gc_obj_size(obj));
    }
}

/* After a mark-stack overflow some marked objects were never scanned:
   rescan every marked, scanned object until no overflow remains. */
static void gc_rescan_marked(void) {
    while (gc.overflow) {
        gc.overflow = 0;
        for (uint32_t i = 0; i < gc.npages; i++) {
            GcPage* p = &gc.pages[i];
            if (p->kind == GC_SMALL) {
                uint32_t size = gc_classes[p->cls], slots = gc_slots(p->cls);
                uint8_t* mm = gc_bm_mark(i);
                uint8_t* ns = gc_bm_noscan(i);
                for (uint32_t k = 0; k < slots; k++) {
                    if (gc_bit(mm, k) && !gc_bit(ns, k)) {
                        uint8_t* obj = gc_page_addr(i) + GC_SMALL_HDR + k * size;
                        gc_scan_range(obj, obj + size);
                        gc_drain();
                    }
                }
            } else if (p->kind == GC_LARGE_HEAD &&
                       (p->lflags & (GC_L_MARK | GC_L_NOSCAN)) == GC_L_MARK) {
                uint8_t* obj = gc_page_addr(i);
                gc_scan_range(obj, obj + (uint64_t)p->n * GC_PAGE);
                gc_drain();
            }
        }
    }
}

/* ── sweep ──────────────────────────────────────────────────────────── */

static void gc_sweep(void) {
    uint64_t live = 0;
    for (int c = 0; c < GC_NCLASSES; c++) gc.partial[c] = 0;
    for (uint32_t i = 0; i < gc.npages; i++) {
        GcPage* p = &gc.pages[i];
        if (p->kind == GC_SMALL) {
            uint8_t* am = gc_bm_alloc(i);
            uint8_t* mm = gc_bm_mark(i);
            uint32_t slots = gc_slots(p->cls);
            uint32_t n = 0;
            for (uint32_t b = 0; b < GC_BITMAP_BYTES; b++) {
                am[b] &= mm[b];
                mm[b] = 0;
                n += (uint32_t)__builtin_popcount(am[b]);
            }
            if (n == 0) {
                gc_release_pages(i, 1);
                continue;
            }
            p->live = (uint16_t)n;
            p->cursor = 0;
            live += (uint64_t)n * gc_classes[p->cls];
            if (n < slots) {
                p->next_partial = gc.partial[p->cls];
                p->listed = 1;
                gc.partial[p->cls] = i + 1;
            } else {
                p->next_partial = 0;
                p->listed = 0;
            }
        } else if (p->kind == GC_LARGE_HEAD) {
            uint32_t n = p->n;
            if (p->lflags & GC_L_MARK) {
                p->lflags &= (uint8_t)~GC_L_MARK;
                live += (uint64_t)n * GC_PAGE;
            } else {
                gc_release_pages(i, n);
            }
            i += n - 1;
        }
    }
    gc.live_bytes = live;
    gc.since_gc = 0;
}

/* ── collection ─────────────────────────────────────────────────────── */

static void gc_collect(const int64_t* extra, int nextra) {
    if (!gc.inited) return;
    gc.msp = 0;
    gc.overflow = 0;
    const uint8_t* self_lo = (const uint8_t*)&gc;
    const uint8_t* self_hi = self_lo + sizeof(gc);
    const uint8_t* dlo = &__global_base;
    const uint8_t* dhi = &__data_end;
    /* The data segment, minus the collector's own state. */
    if (self_lo >= dlo && self_hi <= dhi) {
        gc_scan_range(dlo, self_lo);
        gc_scan_range(self_hi, dhi);
    } else {
        gc_scan_range(dlo, dhi);
    }
    gc_drain();
    /* The live shadow stack: from this frame up to the stack's top. */
    volatile uint32_t here = 0;
    const uint8_t* sp = (const uint8_t*)&here;
    if (sp < &__stack_high) gc_scan_range(sp, &__stack_high);
    gc_drain();
    for (int k = 0; k < nextra; k++) {
        gc_mark_word((uint64_t)(uint32_t)extra[k]);
        gc_drain();
    }
    gc_rescan_marked();
    gc_sweep();
    gc.collections++;
}

static int gc_due(void) {
#ifdef MONAD_GC_STRESS
    return 1;
#else
    uint64_t floor = 8u * 1024u * 1024u;
    uint64_t budget = gc.live_bytes > floor ? gc.live_bytes : floor;
    return gc.since_gc > budget;
#endif
}

/* Frees one block explicitly (ownership-mode drop glue). A word that is
   not the start of a live allocation is a trap: a double free or a wild
   free must not silently corrupt the free lists. */
__attribute__((unused)) static void gc_free(uint64_t v) {
    uint32_t page, slot;
    uint8_t* obj = gc_resolve(v, &page, &slot);
    if (!obj || (uint64_t)(uintptr_t)obj != v) __builtin_trap();
    if (slot == ~0u) {
        gc_release_pages(page, gc.pages[page].n);
        return;
    }
    GcPage* p = &gc.pages[page];
    gc_clr(gc_bm_alloc(page), slot);
    gc_clr(gc_bm_mark(page), slot);
    if (p->live) p->live--;
    if (slot < p->cursor) p->cursor = (uint16_t)slot;
    /* A full page left the partial list on allocation; put it back. */
    if (!p->listed) {
        p->next_partial = gc.partial[p->cls];
        p->listed = 1;
        gc.partial[p->cls] = page + 1;
    }
}

/* ── export boundary ────────────────────────────────────────────────── */

int64_t monad_export_enter(void) {
    gc.depth++;
    return 0;
}

int64_t monad_export_leave(int64_t result) {
    if (gc.depth > 0) gc.depth--;
    if (gc.depth == 0 && gc_due()) gc_collect(&result, 1);
    return result;
}

uint64_t gc_heap_committed(void) {
    return (uint64_t)__builtin_wasm_memory_size(0) * GC_PAGE;
}

uint64_t gc_heap_used(void) {
    return gc.live_bytes + gc.since_gc;
}
