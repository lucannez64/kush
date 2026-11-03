#define _POSIX_C_SOURCE 200112L
#include <stdint.h>
#include <stdlib.h>
void memory_begin(void);
void memory_stage(int64_t);
void memory_end(void);
int main(void) {
    memory_begin();
    void *a=malloc(16),*b=calloc(8,8);
    if(!a||!b)abort();
    memory_stage(1);
    void *grown=realloc(b,128);if(!grown)abort();b=grown;
    memory_stage(2);
    volatile size_t impossible=SIZE_MAX;
    void *refused=realloc(b,impossible);if(refused)abort();
    memory_stage(3);
    void *aligned=aligned_alloc(16,64),*posix=NULL;
    if(!aligned||posix_memalign(&posix,64,128)!=0)abort();
    memory_stage(4);
    free(a);free(b);free(aligned);free(posix);
    memory_end();
    return 0;
}
