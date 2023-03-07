#![feature(associated_type_defaults)]

use hashlink::LinkedHashMap;
use std::cell::RefCell;

pub trait OutputRefAny<'vir, 'tcx> {}
impl<'vir, 'tcx> OutputRefAny<'vir, 'tcx> for () {}

pub enum TaskEncoderCacheState<'vir, 'tcx, E: TaskEncoder + 'vir + ?Sized> {
    // None, // indicated by absence in the cache

    /// Task was enqueued but not yet started.
    Enqueued,

    /// Task is currently being encoded. The output reference is available.
    /// Full encoding is not available yet, and querying for it indicates
    /// a cyclic dependency error.
    Started {
        output_ref: <E as TaskEncoder>::OutputRef<'vir, 'tcx>,
    },

    /// Task was successfully encoded.
    /// TODO: can still collect errors?
    Encoded {
        output_ref: <E as TaskEncoder>::OutputRef<'vir, 'tcx>,
        deps: TaskEncoderDependencies<'vir, 'tcx>,
        output_local: <E as TaskEncoder>::OutputFullLocal<'vir, 'tcx>,
        output_dep: <E as TaskEncoder>::OutputFullDependency<'vir, 'tcx>,
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
        output_ref: <E as TaskEncoder>::OutputRef<'vir, 'tcx>,
        deps: TaskEncoderDependencies<'vir, 'tcx>,
        error: TaskEncoderError<E>,
        output_dep: Option<<E as TaskEncoder>::OutputFullDependency<'vir, 'tcx>>,
    },
}

/// Cache for a task encoder. See `TaskEncoderCacheState` for a description of
/// the possible values in the encoding process.
pub type Cache<'vir, 'tcx, E> = LinkedHashMap<
    <E as TaskEncoder>::TaskKey<'vir, 'tcx>,
    TaskEncoderCacheState<'vir, 'tcx, E>,
>;
pub type CacheRef<'vir, 'tcx, E> = RefCell<Cache<'vir, 'tcx, E>>;

pub type CacheStatic<E> = LinkedHashMap<
    <E as TaskEncoder>::TaskKey<'static, 'static>,
    TaskEncoderCacheState<'static, 'static, E>,
>;
pub type CacheStaticRef<E> = RefCell<CacheStatic<E>>;
/*
pub struct TaskEncoderOutput<'vir, 'tcx, E: TaskEncoder>(
    <E as TaskEncoder>::OutputRef<'vir, 'tcx>,
    <E as TaskEncoder>::TaskKey<'vir, 'tcx>,
)
    where 'tcx: 'vir;

impl<'vir, 'tcx, E: TaskEncoder> TaskEncoderOutput<'vir, 'tcx, E> {
    pub fn get_ref(self) -> <E as TaskEncoder>::OutputRef<'vir, 'tcx> {
        self.0
    }
    pub fn get_output_local(self) -> <E as TaskEncoder>::OutputFullLocal<'vir, 'tcx> {
        todo!()
        //E::encode_full(self.1)
    }
}
*/
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

#[derive(Default)]
pub struct TaskEncoderDependencies<'vir, 'tcx> {
    pub deps_local: Vec<&'vir dyn OutputRefAny<'vir, 'tcx>>,
    pub deps_dep: Vec<&'vir dyn OutputRefAny<'vir, 'tcx>>,
}
impl<'vir, 'tcx> TaskEncoderDependencies<'vir, 'tcx> {
    pub fn require_ref<E: TaskEncoder + 'vir>(
        &mut self,
        task: <E as TaskEncoder>::TaskDescription<'vir, 'tcx>,
    ) -> Result<
        <E as TaskEncoder>::OutputRef<'vir, 'tcx>,
        TaskEncoderError<E>,
    > {
        E::encode_ref(task)
    }

    pub fn require_local<E: TaskEncoder + 'vir>(
        &mut self,
        task: <E as TaskEncoder>::TaskDescription<'vir, 'tcx>,
    ) -> Result<
        <E as TaskEncoder>::OutputFullLocal<'vir, 'tcx>,
        TaskEncoderError<E>,
    > {
        E::encode(task).map(|(_output_ref, output_local, _output_dep)| output_local)
    }

    pub fn require_dep<E: TaskEncoder + 'vir>(
        &mut self,
        task: <E as TaskEncoder>::TaskDescription<'vir, 'tcx>,
    ) -> Result<
        <E as TaskEncoder>::OutputFullDependency<'vir, 'tcx>,
        TaskEncoderError<E>,
    > {
        E::encode(task).map(|(_output_ref, _output_local, output_dep)| output_dep)
    }

    // TODO: ideally not pub?
    pub fn emit_output_ref<E: TaskEncoder + 'vir>(
        &mut self,
        task_key: E::TaskKey<'vir, 'tcx>,
        output_ref: E::OutputRef<'vir, 'tcx>,
    ) {
        assert!(E::with_cache(move |cache| matches!(cache.borrow_mut().insert(
            task_key,
            TaskEncoderCacheState::Started { output_ref },
        ), Some(TaskEncoderCacheState::Enqueued))));
    }
}

pub trait TaskEncoder {
    /// Description of a task to be performed. Should be easily obtained by
    /// clients of this encoder.
    type TaskDescription<'vir, 'tcx>: std::hash::Hash + Eq + Clone + std::fmt::Debug
        where 'tcx: 'vir;

    /// Cache key for a task to be performed. May differ from `TaskDescription`,
    /// for example if the description should be normalised or some non-trivial
    /// resolution needs to happen. In other words, multiple descriptions may
    /// lead to the same key and hence the same output.
    type TaskKey<'vir, 'tcx>: std::hash::Hash + Eq + Clone + std::fmt::Debug = Self::TaskDescription<'vir, 'tcx>
        where 'tcx: 'vir;

    /// A reference to an encoded item. Should be non-unit for tasks which can
    /// be "referred" to from other parts of a program, as opposed to tasks
    /// where only the full output matters.
    type OutputRef<'vir, 'tcx>: Clone + OutputRefAny<'vir, 'tcx> = ()
        where 'tcx: 'vir, Self: 'vir;

    /// Fully encoded output for this task. When encoding items which can be
    /// dependencies (such as methods), this output should only be emitted in
    /// one Viper program.
    type OutputFullLocal<'vir, 'tcx>: Clone
        where 'tcx: 'vir;

    /// Fully encoded output for this task for dependents. When encoding items
    /// which can be dependencies (such as methods), this output should be
    /// emitted in each Viper program that depends on this task.
    type OutputFullDependency<'vir, 'tcx>: Clone = ()
        where 'tcx: 'vir;

    type EnqueueingError: Clone + std::fmt::Debug = ();
    type EncodingError: Clone + std::fmt::Debug;

    /// Enters the given function with a reference to the cache for this
    /// encoder.
    fn with_cache<'vir, 'tcx, F, R>(f: F) -> R
        where 'tcx: 'vir, Self: 'vir, F: FnOnce(&'vir CacheRef<'vir, 'tcx, Self>) -> R;

    //fn get_all_outputs() -> Self::CacheRef<'vir, 'tcx> {
    //  todo!()
    //  // while ... { process() } // process items in the queue
    //  //Self::cache()
    //}

    fn enqueue<'vir, 'tcx>(task: Self::TaskDescription<'vir, 'tcx>)
        where 'tcx: 'vir, Self: 'vir
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

    fn encode_ref<'vir, 'tcx>(task: Self::TaskDescription<'vir, 'tcx>) -> Result<
        Self::OutputRef<'vir, 'tcx>,
        TaskEncoderError<Self>,
    >
        where 'tcx: 'vir, Self: 'vir
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

        // is the task enqueued already?
        let task_key_clone = task_key.clone();
        if Self::with_cache(move |cache| cache.borrow().contains_key(&task_key_clone)) {
            // Cyclic dependency error because:
            // 1. An ouput ref was requested for the task,
            // 2. the task was already enqueued, and
            // 3. there is not an output ref available.
            //
            // This would happen if the current encoder directly or indirectly
            // requested the encoding for a task it is already working on,
            // before it called the `emit_output_ref` method.
            return Err(TaskEncoderError::CyclicError);
        }

        Self::encode(task);

        // otherwise, we need to start the encoding
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

    fn encode<'vir, 'tcx>(task: Self::TaskDescription<'vir, 'tcx>) -> Result<(
        Self::OutputRef<'vir, 'tcx>,
        Self::OutputFullLocal<'vir, 'tcx>,
        Self::OutputFullDependency<'vir, 'tcx>,
    ), TaskEncoderError<Self>>
        where 'tcx: 'vir, Self: 'vir
    {
        let task_key = Self::task_to_key(&task);

        // TODO: check for full output first?

        // enqueue
        let task_key_clone = task_key.clone();
        assert!(Self::with_cache(move |cache| cache.borrow_mut().insert(
            task_key_clone,
            TaskEncoderCacheState::Enqueued,
        ).is_none()));

        let mut deps: TaskEncoderDependencies<'vir, 'tcx> = Default::default();
        let encode_result = Self::do_encode_full(&task_key, &mut deps);

        let output_ref = Self::with_cache(|cache| match cache.borrow().get(&task_key) {
            Some(TaskEncoderCacheState::Started { output_ref }) => output_ref.clone(),
            _ => panic!("encoder did not provide output ref"),
        });

        match encode_result {
            Ok((output_local, output_dep)) => {
                Self::with_cache(|cache| cache.borrow_mut().insert(task_key, TaskEncoderCacheState::Encoded {
                    output_ref: output_ref.clone(),
                    deps,
                    output_local: output_local.clone(),
                    output_dep: output_dep.clone(),
                }));
                Ok((
                    output_ref,
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

    /*
    /// Given a task description for this encoder, enqueue it and return the
    /// reference to the output. If the task is already enqueued, the output
    /// reference already exists.
    fn encode<'vir, 'tcx>(task: Self::TaskDescription<'vir, 'tcx>) -> Self::OutputRef<'vir, 'tcx>
        where 'tcx: 'vir, Self: 'vir
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
    fn encode_eager<'vir, 'tcx>(task: Self::TaskDescription<'vir, 'tcx>) -> Result<(
        Self::OutputRef<'vir, 'tcx>,
        Self::OutputFullLocal<'vir, 'tcx>,
        Self::OutputFullDependency<'vir, 'tcx>,
    ), TaskEncoderError<Self>>
        where 'tcx: 'vir, Self: 'vir
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
    fn encode_full<'vir, 'tcx>(task_key: Self::TaskKey<'vir, 'tcx>) -> Result<(
        Self::OutputFullLocal<'vir, 'tcx>,
        Self::OutputFullDependency<'vir, 'tcx>,
    ), TaskEncoderError<Self>>
        where 'tcx: 'vir, Self: 'vir
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

        let mut deps: TaskEncoderDependencies<'vir, 'tcx> = Default::default();
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
    fn task_to_key<'vir, 'tcx>(task: &Self::TaskDescription<'vir, 'tcx>) -> // Result<
        Self::TaskKey<'vir, 'tcx>//,
    //    Self::EnqueueingError,
    //>
        where 'tcx: 'vir;
/*
    /// Given a task description, create a reference to the output.
    fn task_to_output_ref<'vir, 'tcx>(task: &Self::TaskDescription<'vir, 'tcx>) -> Self::OutputRef<'vir, 'tcx>
        where 'tcx: 'vir;
*/
    fn do_encode_full<'vir, 'tcx>(
        task_key: &Self::TaskKey<'vir, 'tcx>,
        deps: &mut TaskEncoderDependencies<'vir, 'tcx>,
    ) -> Result<(
        Self::OutputFullLocal<'vir, 'tcx>,
        Self::OutputFullDependency<'vir, 'tcx>,
    ), (
        Self::EncodingError,
        Option<Self::OutputFullDependency<'vir, 'tcx>>,
    )>;
}

/*
/// TODO: the implementation always looks the same but cannot be provided as
///   a default implementation in the trait, because of how generics interact
///   with const/static items. Could this be a derive for a separate trait?
#[macro_export]
macro_rules! encoder_cache {
    ($encoder: ty) => {
        fn cache<'vir, 'tcx>() -> $crate::CacheRef<'vir, 'tcx, Self> {
            const CACHE: once_cell::unsync::Lazy<$crate::CacheStaticRef<$encoder>>
                = once_cell::unsync::Lazy::new(|| { println!("lazy construction"); Default::default() });
            // SAFETY: the 'vir and 'tcx given to this function will always be
            //   the same (or shorter) than the lifetimes of the VIR arena and
            //   the rustc type context, respectively
            unsafe { std::mem::transmute((*CACHE).clone()) }
        }
    };
}
*/
