//! Instrumented builds only. The measured runtime binaries do not include this.
//! Counts requested allocations in the workload window, not allocator metadata
//! or pages retained by libc. All underlying allocation is delegated to System.
use std::alloc::{GlobalAlloc, Layout, System};
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering::SeqCst};
static TRACK: AtomicBool = AtomicBool::new(false);
static ALLOCS: AtomicUsize = AtomicUsize::new(0);
static FREES: AtomicUsize = AtomicUsize::new(0);
static REALLOCS: AtomicUsize = AtomicUsize::new(0);
static LIVE: AtomicUsize = AtomicUsize::new(0);
static PEAK: AtomicUsize = AtomicUsize::new(0);
struct Counting;
#[global_allocator]
static GLOBAL: Counting = Counting;
fn grow(bytes: usize) {
    let live = LIVE.fetch_add(bytes, SeqCst) + bytes;
    PEAK.fetch_max(live, SeqCst);
}
// Safety: identical pointer/layout operations are forwarded to System. Only
// atomic bookkeeping is added; it does not allocate or change returned blocks.
unsafe impl GlobalAlloc for Counting {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        let ptr = unsafe { System.alloc(layout) };
        if !ptr.is_null() && TRACK.load(SeqCst) {
            ALLOCS.fetch_add(1, SeqCst);
            grow(layout.size());
        }
        ptr
    }
    unsafe fn alloc_zeroed(&self, layout: Layout) -> *mut u8 {
        let ptr = unsafe { System.alloc_zeroed(layout) };
        if !ptr.is_null() && TRACK.load(SeqCst) {
            ALLOCS.fetch_add(1, SeqCst);
            grow(layout.size());
        }
        ptr
    }
    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        if TRACK.load(SeqCst) {
            FREES.fetch_add(1, SeqCst);
            LIVE.fetch_sub(layout.size(), SeqCst);
        }
        unsafe {
            System.dealloc(ptr, layout);
        }
    }
    unsafe fn realloc(&self, ptr: *mut u8, layout: Layout, size: usize) -> *mut u8 {
        let result = unsafe { System.realloc(ptr, layout, size) };
        if !result.is_null() && TRACK.load(SeqCst) {
            REALLOCS.fetch_add(1, SeqCst);
            if size >= layout.size() {
                grow(size - layout.size());
            } else {
                LIVE.fetch_sub(layout.size() - size, SeqCst);
            }
        }
        result
    }
}
pub fn start() {
    TRACK.store(true, SeqCst);
}
pub fn stop() {
    TRACK.store(false, SeqCst);
}
pub fn report() {
    eprintln!(
        "rust-alloc: allocations={} deallocations={} reallocations={} live-bytes={} peak-requested-bytes={}",
        ALLOCS.load(SeqCst),
        FREES.load(SeqCst),
        REALLOCS.load(SeqCst),
        LIVE.load(SeqCst),
        PEAK.load(SeqCst)
    );
}
