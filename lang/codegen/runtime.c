#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <stdio.h>

void* monad_alloc(size_t size) {
    void* ptr = malloc(size);
    return ptr;
}

void monad_retain(void* ptr) {
    (void)ptr;
}

void monad_release(void* ptr) {
    if (ptr) free(ptr);
}

void* alloc_closure(void* entry, int64_t arity, int64_t env_size) {
    (void)entry; (void)arity; (void)env_size;
    return 0;
}

void* alloc_constructor(int64_t tag, int64_t field_count) {
    (void)tag; (void)field_count;
    return 0;
}

void* alloc_string(char* data, int64_t length) {
    (void)data; (void)length;
    return 0;
}

void monad_print_str(char* s) {
    if (s) printf("%s\n", s);
}

int64_t main_monad(void);

int main(int argc, char** argv) {
    (void)argc;
    (void)argv;
    return (int)main_monad();
}

