use super::*;

pub enum TaskEncoderCacheState<'vir, E: TaskEncoder + 'vir + ?Sized> {
    // None, // indicated by absence in the cache
    /// Task was enqueued but not yet started.
    Enqueued,

    /// Task is currently being encoded. The output reference is available.
    /// Full encoding is not available yet, and querying for it indicates
    /// a cyclic dependency error.
    Started {
        output_ref: <E as TaskEncoder>::OutputRef<'vir>,
    },

    /// Task was successfully encoded.
    /// TODO: can still collect errors?
    Encoded {
        output_ref: <E as TaskEncoder>::OutputRef<'vir>,
        deps: TaskEncoderDependencies<'vir, E>,
        output_local: <E as TaskEncoder>::OutputFullLocal<'vir>,
        output_dep: <E as TaskEncoder>::OutputFullDependency<'vir>,
    },

    /// An error occurred when enqueing the task.
    ErrorEnqueue {
        error: TaskEncoderError<E>,
        spans: Vec<Span>,
    },

    /// An error occurred when encoding the task. The full "local" encoding is
    /// not available. However, tasks which depend on this task may still
    /// succeed, so the encoding for dependents may be present.
    ///
    /// As an example, encoding a method may fail, but it may still be possible
    /// to encode its signature, to be included in dependents' programs.
    ErrorEncode {
        output_ref: <E as TaskEncoder>::OutputRef<'vir>,
        deps: TaskEncoderDependencies<'vir, E>,
        error: TaskEncoderError<E>,
        output_dep: Option<<E as TaskEncoder>::OutputFullDependency<'vir>>,
        spans: Vec<Span>,
    },
}

/// Cache for a task encoder. See `TaskEncoderCacheState` for a description of
/// the possible values in the encoding process.
pub type Cache<'vir, E> =
    FxIndexMap<<E as TaskEncoder>::TaskKey<'vir>, TaskEncoderCacheState<'vir, E>>;
pub type CacheRef<'vir, E> = RefCell<Cache<'vir, E>>;

pub type CacheStatic<E> =
    FxIndexMap<<E as TaskEncoder>::TaskKey<'static>, TaskEncoderCacheState<'static, E>>;
pub type CacheStaticRef<E> = RefCell<CacheStatic<E>>;

/// Create the cache storage (a static `RefCell`) and a `with_cache`
/// implementation within a `TaskEncoder` `impl` block. This should always be
/// placed at the beginning of the `impl` block for consistency.
///
/// (Implementation notes: the implementation is always the same. However, it
/// cannot be a method provided by the trait, because such an implementation
/// would only create a single static; each cache storage must syntactically
/// differ. A supertrait of `TaskEncoder` which only contains the cache and
/// has a derive macro *might* work, but the `CacheRef` etc types make this a
/// bit difficult without introducing a cyclic dependency in the two traits.)
#[macro_export]
macro_rules! encoder_cache {
    ($encoder: ty) => {
        fn with_cache<'vir, F, R>(f: F) -> R
            where F: FnOnce(&'vir $crate::CacheRef<'vir, $encoder>) -> R,
        {
            ::std::thread_local! {
                static CACHE: $crate::CacheStaticRef<$encoder> = ::std::cell::RefCell::new(Default::default());
            }
            CACHE.with(|cache| {
                // SAFETY: the 'vir and 'tcx given to this function will always be
                //   the same (or shorter) than the lifetimes of the VIR arena and
                //   the rustc type context, respectively
                let cache = unsafe { ::std::mem::transmute(cache) };
                f(cache)
            })
        }

        fn with_watchers<'vir, F, R>(f: F) -> R
            where F: FnOnce(&'vir $crate::WatchersRef<'vir, $encoder>) -> R,
        {
            ::std::thread_local! {
                static WATCHERS: $crate::WatchersStaticRef<$encoder> = ::std::cell::RefCell::new(Default::default());
            }
            WATCHERS.with(|watchers| {
                // SAFETY: as for the cache above
                let watchers = unsafe { ::std::mem::transmute(watchers) };
                f(watchers)
            })
        }
    };
}
