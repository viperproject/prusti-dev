#![feature(associated_type_defaults)]

use hashlink::LinkedHashMap;
use std::{cell::RefCell, marker::PhantomData};

pub trait OutputRefAny {}
impl OutputRefAny for () {}

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
    },
}

/// Cache for a task encoder. See `TaskEncoderCacheState` for a description of
/// the possible values in the encoding process.
pub type Cache<'vir, E> = LinkedHashMap<
    <E as TaskEncoder>::TaskKey<'vir>,
    TaskEncoderCacheState<'vir, E>,
>;
pub type CacheRef<'vir, E> = RefCell<Cache<'vir, E>>;

pub type CacheStatic<E> = LinkedHashMap<
    <E as TaskEncoder>::TaskKey<'static>,
    TaskEncoderCacheState<'static, E>,
>;
pub type CacheStaticRef<E> = RefCell<CacheStatic<E>>;
/*
pub struct TaskEncoderOutput<'vir, E: TaskEncoder>(
    <E as TaskEncoder>::OutputRef<'vir>,
    <E as TaskEncoder>::TaskKey<'vir>,
)
    where 'tcx: 'vir;

impl<'vir, E: TaskEncoder> TaskEncoderOutput<'vir, E> {
    pub fn get_ref(self) -> <E as TaskEncoder>::OutputRef<'vir> {
        self.0
    }
    pub fn get_output_local(self) -> <E as TaskEncoder>::OutputFullLocal<'vir> {
        todo!()
        //E::encode_full(self.1)
    }
}
*/

/// The result of the actual encoder implementation (`do_encode_full`).
pub type EncodeFullResult<'vir, E: TaskEncoder + 'vir + ?Sized> = Result<(
    E::OutputFullLocal<'vir>,
    E::OutputFullDependency<'vir>,
), EncodeFullError<'vir, E>>;

/// An unsuccessful result occurring in `do_encode_full`.
pub enum EncodeFullError<'vir, E: TaskEncoder + 'vir + ?Sized> {
    /// Indicates that the current task has already been encoded. This can
    /// occur when there are cyclic dependencies between multiple encoders.
    /// This error is specifically returned when one encoder depends on
    /// another encoder (using e.g. `TaskEncoderDependencies::require_ref`),
    /// that latter encoder then depending on the former again, causing the
    /// former encoder to complete its full encoding in the inner invocation.
    /// The outer invocation remains on the stack, but will be aborted early
    /// as soon as the control flow returns to it.
    AlreadyEncoded,

    /// An actual error occurred during encoding.
    EncodingError(<E as TaskEncoder>::EncodingError, Option<E::OutputFullDependency<'vir>>),

    DependencyError,
}

// Manual implementation, since neither `E` nor `E::OutputFullDependency` are
// required to be `Debug`.
impl<'vir, E: TaskEncoder + 'vir + ?Sized> std::fmt::Debug for EncodeFullError<'vir, E> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::AlreadyEncoded => write!(f, "AlreadyEncoded"),
            Self::EncodingError(err, _output_dep) => f.debug_tuple("EncodingError").field(err)/*.field(output_dep)*/.finish(),
            Self::DependencyError => write!(f, "DependencyError"),
        }
    }
}

pub enum TaskEncoderError<E: TaskEncoder + ?Sized> {
    EnqueueingError(<E as TaskEncoder>::EnqueueingError),
    EncodingError(<E as TaskEncoder>::EncodingError),
    // TODO: error of another task encoder?
    CyclicError,
}

impl<E: TaskEncoder + ?Sized> std::fmt::Debug for TaskEncoderError<E>
    where <E as TaskEncoder>::EncodingError: std::fmt::Debug
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut helper = f.debug_struct("TaskEncoderError");
        match self {
            Self::EncodingError(err) => helper.field("EncodingError", err),
            Self::EnqueueingError(err) => helper.field("EnqueueingError", err),
            Self::CyclicError => helper.field("CyclicError", &""),
        };
        helper.finish()
    }
}

// manual implementation because derive adds Clone on all generic parameters
impl<E: TaskEncoder + ?Sized> Clone for TaskEncoderError<E> {
    fn clone(&self) -> Self {
        match self {
            Self::EncodingError(err) => Self::EncodingError(err.clone()),
            Self::EnqueueingError(err) => Self::EnqueueingError(err.clone()),
            Self::CyclicError => Self::CyclicError,
        }
    }
}

pub struct TaskEncoderDependencies<'vir, E: TaskEncoder + 'vir + ?Sized> {
    _marker: PhantomData<E>,
    task_key: Option<E::TaskKey<'vir>>,
    pub deps_local: Vec<&'vir dyn OutputRefAny>,
    pub deps_dep: Vec<&'vir dyn OutputRefAny>,
}
impl<'vir, E: TaskEncoder + 'vir + ?Sized> TaskEncoderDependencies<'vir, E> {
    fn check_cycle(&self) -> Result<(), EncodeFullError<'vir, E>> {
        if let Some(task_key) = self.task_key.as_ref() {
            if E::with_cache(move |cache| matches!(
                cache.borrow().get(task_key),
                Some(TaskEncoderCacheState::Encoded { .. }
                    | TaskEncoderCacheState::ErrorEncode { .. }
                    | TaskEncoderCacheState::ErrorEnqueue { .. }),
            )) {
                return Err(EncodeFullError::AlreadyEncoded);
            }
        }
        Ok(())
    }

    pub fn require_ref<EOther: TaskEncoder>(
        &mut self,
        task: <EOther as TaskEncoder>::TaskDescription<'vir>,
    ) -> Result<
        <EOther as TaskEncoder>::OutputRef<'vir>,
        EncodeFullError<'vir, E>,
    > {
        EOther::encode_ref(task)
            .map_err(|_| EncodeFullError::DependencyError)
            .and_then(|result| {
                self.check_cycle()?;
                Ok(result)
            })
    }

    pub fn require_local<EOther: TaskEncoder + 'vir>(
        &mut self,
        task: <EOther as TaskEncoder>::TaskDescription<'vir>,
    ) -> Result<
        <EOther as TaskEncoder>::OutputFullLocal<'vir>,
        EncodeFullError<'vir, E>,
    > {
        EOther::encode(task, true)
            .map(Option::unwrap)
            .map(|(_output_ref, output_local, _output_dep)| output_local)
            .map_err(|_| EncodeFullError::DependencyError)
            .and_then(|result| {
                self.check_cycle()?;
                Ok(result)
            })
    }

    pub fn require_dep<EOther: TaskEncoder + 'vir>(
        &mut self,
        task: <EOther as TaskEncoder>::TaskDescription<'vir>,
    ) -> Result<
        <EOther as TaskEncoder>::OutputFullDependency<'vir>,
        EncodeFullError<'vir, E>,
    > {
        EOther::encode(task, true)
            .map(Option::unwrap)
            .map(|(_output_ref, _output_local, output_dep)| output_dep)
            .map_err(|_| EncodeFullError::DependencyError)
            .and_then(|result| {
                self.check_cycle()?;
                Ok(result)
            })
    }

    pub fn emit_output_ref(
        &mut self,
        task_key: E::TaskKey<'vir>,
        output_ref: E::OutputRef<'vir>,
    ) -> Result<(), EncodeFullError<'vir, E>> {
        assert!(self.task_key.replace(task_key.clone()).is_none(), "output ref already set for task key {task_key:?}");
        self.check_cycle()?;
        assert!(E::with_cache(move |cache| matches!(cache.borrow_mut().insert(
            task_key,
            TaskEncoderCacheState::Started { output_ref },
        ), Some(TaskEncoderCacheState::Enqueued
            | TaskEncoderCacheState::Started { .. }))));
        Ok(())
    }
}

pub trait TaskEncoder {
    /// Description of a task to be performed. Should be easily obtained by
    /// clients of this encoder.
    type TaskDescription<'vir>: std::hash::Hash + Eq + Clone + std::fmt::Debug;

    /// Cache key for a task to be performed. May differ from `TaskDescription`,
    /// for example if the description should be normalised or some non-trivial
    /// resolution needs to happen. In other words, multiple descriptions may
    /// lead to the same key and hence the same output.
    type TaskKey<'vir>: std::hash::Hash + Eq + Clone + std::fmt::Debug = Self::TaskDescription<'vir>;

    /// A reference to an encoded item. Should be non-unit for tasks which can
    /// be "referred" to from other parts of a program, as opposed to tasks
    /// where only the full output matters.
    type OutputRef<'vir>: Clone + OutputRefAny = ()
        where Self: 'vir;

    /// Fully encoded output for this task. When encoding items which can be
    /// dependencies (such as methods), this output should only be emitted in
    /// one Viper program.
    type OutputFullLocal<'vir>: Clone
        where Self: 'vir;

    /// Fully encoded output for this task for dependents. When encoding items
    /// which can be dependencies (such as methods), this output should be
    /// emitted in each Viper program that depends on this task.
    type OutputFullDependency<'vir>: Clone = ()
        where Self: 'vir;

    type EnqueueingError: Clone + std::fmt::Debug = ();
    type EncodingError: Clone + std::fmt::Debug;

    /// Enters the given function with a reference to the cache for this
    /// encoder.
    fn with_cache<'vir, F, R>(f: F) -> R
        where Self: 'vir, F: FnOnce(&'vir CacheRef<'vir, Self>) -> R;

    //fn get_all_outputs() -> Self::CacheRef<'vir> {
    //  todo!()
    //  // while ... { process() } // process items in the queue
    //  //Self::cache()
    //}

    fn enqueue<'vir>(task: Self::TaskDescription<'vir>)
        where Self: 'vir
    {
        let task_key = Self::task_to_key(&task);
        let task_key_clone = task_key.clone(); // TODO: remove?

        if Self::with_cache(move |cache| cache.borrow().contains_key(&task_key_clone)) {
            return;
        }

        // enqueue, expecting no entry (we just checked)
        assert!(Self::with_cache(move |cache| cache.borrow_mut().insert(
            task_key,
            TaskEncoderCacheState::Enqueued,
        ).is_none()));
    }

    fn encode_ref<'vir>(task: Self::TaskDescription<'vir>) -> Result<
        Self::OutputRef<'vir>,
        TaskEncoderError<Self>,
    >
        where Self: 'vir
    {
        let task_key = Self::task_to_key(&task);

        // is there an output ref available already?
        let task_key_clone = task_key.clone();
        if let Some(output_ref) = Self::with_cache(move |cache| match cache.borrow().get(&task_key_clone) {
            Some(TaskEncoderCacheState::Started { output_ref, .. })
            | Some(TaskEncoderCacheState::Encoded { output_ref, .. })
            | Some(TaskEncoderCacheState::ErrorEncode { output_ref, .. }) => Some(output_ref.clone()),
            _ => None,
        }) {
            return Ok(output_ref);
        }

        // Otherwise, we need to start the encoding. Note that this is done
        // even if the encoding was started previously, i.e. if the cache
        // contains a `Enqueued` entry for this task. This can happen if the
        // same task was (recursively) requested from the same encoder, before
        // its first invocation reached a call to `emit_output_ref`.
        // TODO: we should still make sure that *some* progress is done, because an actual cyclic dependency could cause a stack overflow?
        Self::encode(task, false)?;

        let task_key_clone = task_key.clone();
        if let Some(output_ref) = Self::with_cache(move |cache| match cache.borrow().get(&task_key_clone) {
            Some(TaskEncoderCacheState::Started { output_ref, .. })
            | Some(TaskEncoderCacheState::Encoded { output_ref, .. })
            | Some(TaskEncoderCacheState::ErrorEncode { output_ref, .. }) => Some(output_ref.clone()),
            _ => None,
        }) {
            return Ok(output_ref);
        }

        panic!("output ref not found after encoding") // TODO: error?
    }

    fn encode<'vir>(task: Self::TaskDescription<'vir>, need_output: bool) -> Result<Option<(
        Self::OutputRef<'vir>,
        Self::OutputFullLocal<'vir>,
        Self::OutputFullDependency<'vir>,
    )>, TaskEncoderError<Self>>
        where Self: 'vir
    {
        let task_key = Self::task_to_key(&task);

        let in_cache = Self::with_cache(|cache| {
            let mut cache = cache.borrow_mut();

            match cache.get(&task_key) {
                Some(e) => match e {
                    TaskEncoderCacheState::ErrorEnqueue { error }
                    | TaskEncoderCacheState::ErrorEncode { error, .. } => Some(Err(error.clone())),
                    TaskEncoderCacheState::Encoded {
                        output_ref,
                        output_local,
                        output_dep,
                        ..
                    } => if need_output {
                        Some(Ok(Some((
                            output_ref.clone(),
                            output_local.clone(),
                            output_dep.clone(),
                        ))))
                    } else {
                        Some(Ok(None))
                    }
                    // TODO: should we return Some(Ok(None)) for `Started`, if `!need_output` ?
                    TaskEncoderCacheState::Enqueued | TaskEncoderCacheState::Started { .. } => None,
                },
                None => {
                    // enqueue
                    cache.insert(task_key.clone(), TaskEncoderCacheState::Enqueued);
                    None
                }
            }
        });
        if let Some(in_cache) = in_cache {
            return in_cache;
        }

        let mut deps = TaskEncoderDependencies {
            _marker: PhantomData,
            task_key: None,
            deps_local: vec![],
            deps_dep: vec![],
        };
        let encode_result = Self::do_encode_full(&task_key, &mut deps);

        let output_ref = Self::with_cache(|cache| match cache.borrow().get(&task_key) {
            Some(TaskEncoderCacheState::Started { output_ref }
                | TaskEncoderCacheState::Encoded { output_ref, .. }) => output_ref.clone(),
            _ => panic!("encoder did not provide output ref for task {task_key:?}"),
        });

        match encode_result {
            Ok((output_local, output_dep)) => {
                if need_output {
                    Self::with_cache(|cache| cache.borrow_mut().insert(task_key, TaskEncoderCacheState::Encoded {
                        output_ref: output_ref.clone(),
                        deps,
                        output_local: output_local.clone(),
                        output_dep: output_dep.clone(),
                    }));
                    Ok(Some((
                        output_ref,
                        output_local,
                        output_dep,
                    )))
                } else {
                    Self::with_cache(|cache| cache.borrow_mut().insert(task_key, TaskEncoderCacheState::Encoded {
                        output_ref: output_ref,
                        deps,
                        output_local: output_local,
                        output_dep: output_dep,
                    }));
                    Ok(None)
                }
            }
            Err(EncodeFullError::AlreadyEncoded) => Self::with_cache(|cache| match cache.borrow().get(&task_key).unwrap() {
                TaskEncoderCacheState::Encoded {
                    output_ref,
                    output_local,
                    output_dep,
                    ..
                } => if need_output {
                    Ok(Some((
                        // TODO: does it even make sense for an encoder to request the full encoding
                        //   when a cycle can occur?
                        output_ref.clone(),
                        output_local.clone(),
                        output_dep.clone(),
                    )))
                } else {
                    Ok(None)
                },
                TaskEncoderCacheState::ErrorEnqueue { error }
                | TaskEncoderCacheState::ErrorEncode { error, .. } => Err(error.clone()),
                TaskEncoderCacheState::Started { .. }
                | TaskEncoderCacheState::Enqueued => panic!("encoder did not finish for task {task_key:?}"),
            }),
            Err(EncodeFullError::DependencyError) => todo!(),
            Err(EncodeFullError::EncodingError(err, maybe_output_dep)) => {
                Self::with_cache(|cache| cache.borrow_mut().insert(task_key, TaskEncoderCacheState::ErrorEncode {
                    output_ref: output_ref.clone(),
                    deps,
                    error: TaskEncoderError::EncodingError(err.clone()),
                    output_dep: maybe_output_dep,
                }));
                Err(TaskEncoderError::EncodingError(err))
            }
        }
    }

    /*
    /// Given a task description for this encoder, enqueue it and return the
    /// reference to the output. If the task is already enqueued, the output
    /// reference already exists.
    fn encode<'vir>(task: Self::TaskDescription<'vir>) -> Self::OutputRef<'vir>
        where Self: 'vir
    {
        let task_key = Self::task_to_key(&task);
        let task_key_clone = task_key.clone();
        if let Some(output_ref) = Self::with_cache(move |cache| match cache.borrow().get(&task_key_clone) {
            Some(TaskEncoderCacheState::Enqueued { output_ref })
            | Some(TaskEncoderCacheState::Started { output_ref, .. })
            | Some(TaskEncoderCacheState::Encoded { output_ref, .. })
            | Some(TaskEncoderCacheState::ErrorEncode { output_ref, .. }) => Some(output_ref.clone()),
            _ => None,
        }) {
            return output_ref;
        }
        let task_ref = Self::task_to_output_ref(&task);
        let task_key_clone = task_key.clone();
        let task_ref_clone = task_ref.clone();
        assert!(Self::with_cache(move |cache| cache.borrow_mut().insert(
            task_key_clone,
            TaskEncoderCacheState::Enqueued { output_ref: task_ref_clone },
        ).is_none()));
        task_ref
    }

    // TODO: this function should not be needed
    fn encode_eager<'vir>(task: Self::TaskDescription<'vir>) -> Result<(
        Self::OutputRef<'vir>,
        Self::OutputFullLocal<'vir>,
        Self::OutputFullDependency<'vir>,
    ), TaskEncoderError<Self>>
        where Self: 'vir
    {
        let task_key = Self::task_to_key(&task);
        // enqueue
        let output_ref = Self::encode(task);
        // process
        Self::encode_full(task_key)
            .map(|(output_full_local, output_full_dep)| (output_ref, output_full_local, output_full_dep))
    }

    /// Given a task key, fully encode the given task. If this task was already
    /// finished, the encoding is not repeated. If this task was enqueued, but
    /// not finished, return a `CyclicError`.
    fn encode_full<'vir>(task_key: Self::TaskKey<'vir>) -> Result<(
        Self::OutputFullLocal<'vir>,
        Self::OutputFullDependency<'vir>,
    ), TaskEncoderError<Self>>
        where Self: 'vir
    {
        let mut output_ref_opt = None;
        let ret = Self::with_cache(|cache| {
            // should be queued by now
            match cache.borrow().get(&task_key).unwrap() {
                TaskEncoderCacheState::Enqueued { output_ref } => {
                    output_ref_opt = Some(output_ref.clone());
                    None
                }
                TaskEncoderCacheState::Started { .. } => Some(Err(TaskEncoderError::CyclicError)),
                TaskEncoderCacheState::Encoded { output_local, output_dep, .. } =>
                    Some(Ok((
                        output_local.clone(),
                        output_dep.clone(),
                    ))),
                TaskEncoderCacheState::ErrorEncode { error, .. } =>
                    Some(Err(error.clone())),
            }
        });
        if let Some(ret) = ret {
            return ret;
        }
        let output_ref = output_ref_opt.unwrap();

        let mut deps: TaskEncoderDependencies<'vir> = Default::default();
        match Self::do_encode_full(&task_key, &mut deps) {
            Ok((output_local, output_dep)) => {
                Self::with_cache(|cache| cache.borrow_mut().insert(task_key, TaskEncoderCacheState::Encoded {
                    output_ref: output_ref.clone(),
                    deps,
                    output_local: output_local.clone(),
                    output_dep: output_dep.clone(),
                }));
                Ok((
                    output_local,
                    output_dep,
                ))
            }
            Err((err, maybe_output_dep)) => {
                Self::with_cache(|cache| cache.borrow_mut().insert(task_key, TaskEncoderCacheState::ErrorEncode {
                    output_ref: output_ref.clone(),
                    deps,
                    error: TaskEncoderError::EncodingError(err.clone()),
                    output_dep: maybe_output_dep,
                }));
                Err(TaskEncoderError::EncodingError(err))
            }
        }
    }
*/
    /// Given a task description, create a key for storing it in the cache.
    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> // Result<
        Self::TaskKey<'vir>;//,
    //    Self::EnqueueingError,
    //>
/*
    /// Given a task description, create a reference to the output.
    fn task_to_output_ref<'vir>(task: &Self::TaskDescription<'vir>) -> Self::OutputRef<'vir>;
*/
    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self>;

    fn all_outputs<'vir>() -> Vec<Self::OutputFullLocal<'vir>>
        where Self: 'vir
    {
        Self::with_cache(|cache| {
            let mut ret = vec![];
            for (_task_key, cache_state) in cache.borrow().iter() {
                match cache_state { // TODO: make this into an iterator chain
                    TaskEncoderCacheState::Encoded { output_local, .. } => ret.push(output_local.clone()),
                    _ => {}
                }
            }
            ret
        })
    }
}

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
    };
}
