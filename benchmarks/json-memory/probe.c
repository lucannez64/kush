#define _GNU_SOURCE
#include <stdint.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <fcntl.h>
#include <string.h>
#ifdef TRACE_ALLOC
#include <malloc.h>
/* Fixed storage: instrumentation never allocates. It is absent from timing
   and RSS binaries. Linker wrapping sees calls from executable/static objects,
   not hidden allocation inside shared libc. These are allocator requests,
   not mmap/brk counts or total resident memory. */
#define SLOTS ((size_t)1 << 19)
typedef struct { void *pointer; size_t requested, usable; int workload; } Entry;
static Entry entries[SLOTS];
static int active, ended;
static uint64_t alloc_calls, realloc_calls, realloc_in_place, realloc_moved, freed_active, freed_after;
static uint64_t requested_total, live_requested, live_usable, peak_requested, peak_usable;
static uint64_t baseline_requested, baseline_usable, workload_live_requested, workload_live_allocations;
static void die(void) { const char message[]="memory probe table overflow\n"; (void)write(2,message,sizeof(message)-1); _Exit(3); }
static size_t slot(void *pointer) { uintptr_t n=(uintptr_t)pointer >> 4;return (size_t)(n^(n>>19))&(SLOTS-1); }
static Entry *find(void *pointer) {
    size_t at=slot(pointer);
    for(size_t n=0;n<SLOTS;n++,at=(at+1)&(SLOTS-1)){
        if(entries[at].pointer==NULL)return NULL;
        if(entries[at].pointer==pointer)return &entries[at];
    }
    return NULL;
}
static void remember(void *pointer,size_t size) {
    if(pointer==NULL||ended)return;
    size_t at=slot(pointer),available=SLOTS;
    for(size_t n=0;n<SLOTS;n++,at=(at+1)&(SLOTS-1)){
        if(entries[at].pointer==(void *)(uintptr_t)1&&available==SLOTS)available=at;
        if(entries[at].pointer==NULL){if(available==SLOTS)available=at;break;}
    }
    if(available==SLOTS)die();
    size_t usable=malloc_usable_size(pointer);
    entries[available]=(Entry){pointer,size,usable,active};
    if(active){workload_live_requested+=size;workload_live_allocations++;}
    live_requested+=size;live_usable+=usable;
    if(active){if(live_requested>peak_requested)peak_requested=live_requested;if(live_usable>peak_usable)peak_usable=live_usable;}
}
static int forget(void *pointer,int count) {
    if(pointer==NULL)return 0;
    Entry *entry=find(pointer);if(entry==NULL)return 0;
    live_requested-=entry->requested;live_usable-=entry->usable;
    if(entry->workload){workload_live_requested-=entry->requested;workload_live_allocations--;}
    entry->pointer=(void *)(uintptr_t)1;
    if(count){if(active)freed_active++;else if(ended)freed_after++;}
    return 1;
}
void *__real_malloc(size_t);
void *__real_calloc(size_t,size_t);
void *__real_realloc(void *,size_t);
void *__real_aligned_alloc(size_t,size_t);
int __real_posix_memalign(void **,size_t,size_t);
void __real_free(void *);
void *__wrap_malloc(size_t size) {
    void *pointer=__real_malloc(size);if(pointer&&active){alloc_calls++;requested_total+=size;}remember(pointer,size);return pointer;
}
void *__wrap_calloc(size_t count,size_t size) {
    void *pointer=__real_calloc(count,size);if(pointer&&active){alloc_calls++;requested_total+=count*size;}remember(pointer,count*size);return pointer;
}
void *__wrap_aligned_alloc(size_t alignment,size_t size) {
    void *pointer=__real_aligned_alloc(alignment,size);if(pointer&&active){alloc_calls++;requested_total+=size;}remember(pointer,size);return pointer;
}
int __wrap_posix_memalign(void **out,size_t alignment,size_t size) {
    int result=__real_posix_memalign(out,alignment,size);if(result==0){if(active){alloc_calls++;requested_total+=size;}remember(*out,size);}return result;
}
void __wrap_free(void *pointer) {forget(pointer,1);__real_free(pointer);}
void *__wrap_realloc(void *pointer,size_t size) {
    /* Keep the old integer address only for table identity; never dereference a
       pointer after realloc. Refusal at nonzero size keeps its old entry. */
    uintptr_t previous=(uintptr_t)pointer;
    void *result=__real_realloc(pointer,size);
    if(result!=NULL||size==0){forget((void *)previous,0);if(result){if(active){realloc_calls++;requested_total+=size;if((uintptr_t)result==previous)realloc_in_place++;else realloc_moved++;}remember(result,size);}}
    return result;
}
static void report(int64_t stage) {
    char line[1024];
    int length=snprintf(line,sizeof(line),"memory-alloc: {\"stage\":%lld,\"alloc_calls\":%llu,\"realloc_calls\":%llu,\"realloc_in_place_calls\":%llu,\"realloc_moved_calls\":%llu,\"frees_during_workload\":%llu,\"frees_after_workload\":%llu,\"requested_bytes_total\":%llu,\"live_requested_bytes\":%llu,\"live_usable_bytes\":%llu,\"peak_live_requested_bytes\":%llu,\"peak_live_usable_bytes\":%llu,\"workload_live_requested_bytes\":%llu,\"workload_live_allocations\":%llu,\"baseline_requested_bytes\":%llu,\"baseline_usable_bytes\":%llu}\n",(long long)stage,(unsigned long long)alloc_calls,(unsigned long long)realloc_calls,(unsigned long long)realloc_in_place,(unsigned long long)realloc_moved,(unsigned long long)freed_active,(unsigned long long)freed_after,(unsigned long long)requested_total,(unsigned long long)live_requested,(unsigned long long)live_usable,(unsigned long long)peak_requested,(unsigned long long)peak_usable,(unsigned long long)workload_live_requested,(unsigned long long)workload_live_allocations,(unsigned long long)baseline_requested,(unsigned long long)baseline_usable);
    if(length>0&&(size_t)length<sizeof(line))(void)write(2,line,(size_t)length);
}
static void final_report(void) {report(6);}
#endif
#ifdef PHASE_RSS
static void rss(int64_t stage) {
    char buffer[2048],line[256];int fd=open("/proc/self/status",O_RDONLY);if(fd<0)_Exit(4);
    ssize_t count=read(fd,buffer,sizeof(buffer)-1);close(fd);if(count<0)_Exit(4);buffer[count]='\0';
    char *current=strstr(buffer,"VmRSS:"),*peak=strstr(buffer,"VmHWM:");if(!current||!peak)_Exit(4);
    unsigned long resident=strtoul(current+6,NULL,10),high=strtoul(peak+6,NULL,10);
    int length=snprintf(line,sizeof(line),"memory-rss: {\"stage\":%lld,\"rss_kib\":%lu,\"high_water_kib\":%lu}\n",(long long)stage,resident,high);
    if(length>0&&(size_t)length<sizeof(line))(void)write(2,line,(size_t)length);
}
#endif
void memory_begin(void) {
#ifdef TRACE_ALLOC
    active=1;baseline_requested=live_requested;baseline_usable=live_usable;peak_requested=live_requested;peak_usable=live_usable;
    if(atexit(final_report)!=0)_Exit(4);
    report(0);
#endif
#ifdef PHASE_RSS
    rss(0);
#endif
}
void memory_stage(int64_t stage) {
#ifdef TRACE_ALLOC
    report(stage);
#elif defined(PHASE_RSS)
    rss(stage);
#else
    (void)stage;
#endif
}
void memory_end(void) {
#ifdef TRACE_ALLOC
    report(5);active=0;ended=1;
#endif
#ifdef PHASE_RSS
    rss(5);
#endif
}
