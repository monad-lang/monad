#include <stdatomic.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef struct {
    _Atomic(int64_t) refcount;
    uint16_t tag;
    uint16_t flags;
} Header;

typedef struct {
    Header header;
    void* entry;
    int64_t arity;
    int64_t env_size;
    void* env[];
} Closure;

typedef struct {
    Header header;
    int64_t tag;
    int64_t field_count;
    void* fields[];
} Constructor;

typedef struct {
    Header header;
    int64_t length;
    char data[];
} StringObj;

void* monad_alloc(size_t size) {
    void* ptr = malloc(size);
    if (ptr) {
        Header* h = (Header*)ptr;
        h->refcount = 1;
        h->tag = 0;
        h->flags = 0;
    }
    return ptr;
}

void monad_retain(void* ptr) {
    if (!ptr) return;
    Header* h = (Header*)ptr;
    atomic_fetch_add(&h->refcount, 1);
}

void monad_release(void* ptr) {
    if (!ptr) return;
    Header* h = (Header*)ptr;
    if (atomic_fetch_sub(&h->refcount, 1) == 1) {
        free(h);
    }
}

void* alloc_closure(void* entry, int64_t arity, int64_t env_size) {
    size_t size = sizeof(Closure) + env_size * sizeof(void*);
    Closure* c = (Closure*)monad_alloc(size);
    if (c) {
        c->header.tag = 1;
        c->entry = entry;
        c->arity = arity;
        c->env_size = env_size;
    }
    return c;
}

void* alloc_constructor(int64_t tag, int64_t field_count) {
    size_t size = sizeof(Constructor) + field_count * sizeof(void*);
    Constructor* c = (Constructor*)monad_alloc(size);
    if (c) {
        c->header.tag = 2;
        c->tag = tag;
        c->field_count = field_count;
    }
    return c;
}

void* alloc_string(char* data, int64_t length) {
    size_t size = sizeof(StringObj) + length + 1;
    StringObj* s = (StringObj*)monad_alloc(size);
    if (s) {
        s->header.tag = 3;
        s->length = length;
        memcpy(s->data, data, length);
        s->data[length] = '\0';
    }
    return s;
}

void monad_print_str(char* s) {
    if (s) printf("%s\n", s);
}

char* monad_read_file(char* path) {
    if (!path) return NULL;
    FILE* f = fopen(path, "rb");
    if (!f) return NULL;
    fseek(f, 0, SEEK_END);
    long size = ftell(f);
    fseek(f, 0, SEEK_SET);
    if (size < 0) { fclose(f); return NULL; }
    char* buf = (char*)malloc(size + 1);
    if (!buf) { fclose(f); return NULL; }
    size_t got = fread(buf, 1, size, f);
    fclose(f);
    if (got != (size_t)size) { free(buf); return NULL; }
    buf[size] = '\0';
    return buf;
}

void monad_write_file(char* path, char* data, int64_t len) {
    if (!path || !data || len < 0) return;
    FILE* f = fopen(path, "wb");
    if (!f) return;
    fwrite(data, 1, (size_t)len, f);
    fclose(f);
}

char* monad_file_exists(char* path) {
    if (!path) return NULL;
    FILE* f = fopen(path, "rb");
    if (f) { fclose(f); return (char*)"1"; }
    return NULL;
}

/* Build a List String (linked list of StringObj) from command line args.
   List.empty is constructor tag 0 (0 fields).
   List.cons is constructor tag 1 (2 fields: head, tail).
   Strings are built via alloc_string.
   Builds the list in reverse (cons prepends), so argv[0] is first. */
void* monad_build_args(int argc, char** argv) {
    void* list = alloc_constructor(0, 0);   /* List.empty */
    for (int i = argc - 1; i >= 0; i--) {
        void* str = alloc_string(argv[i], (int64_t)strlen(argv[i]));
        Constructor* cons = (Constructor*)alloc_constructor(1, 2);
        cons->fields[0] = str;   /* head */
        cons->fields[1] = list;  /* tail */
        list = cons;
    }
    return list;
}

int64_t main_monad(void* args);

int main(int argc, char** argv) {
    void* args = monad_build_args(argc, argv);
    return (int)main_monad(args);
}
