#![feature(associated_type_defaults)]

use hashlink::LinkedHashMap;
use std::cell::RefCell;

mod cache;
mod dependencies;
mod result;

pub use cache::*;
pub use dependencies::*;
pub use result::*;

pub trait OutputRefAny {}
impl OutputRefAny for () {}

pub trait TaskEncoder {
    /// Description of a task to be performed. Should be easily obtained by
    /// clients of this encoder.
    type TaskDescription<'vir>: std::hash::Hash + Eq + Clone + std::fmt::Debug;

    /// Cache key for a task to be performed. May differ from `TaskDescription`,
    /// for example if the description should be normalised or some non-trivial
    /// resolution needs to happen. In other words, multiple descriptions may
    /// lead to the same key and hence the same output.
    type TaskKey<'vir>: std::hash::Hash + Eq + Clone + std::fmt::Debug =
        Self::TaskDescription<'vir>;

    /// A reference to an encoded item. Should be non-unit for tasks which can
    /// be "referred" to from other parts of a program, as opposed to tasks
    /// where only the full output matters.
    type OutputRef<'vir>: Clone + OutputRefAny
        = ()
    where
        Self: 'vir;

    /// Fully encoded output for this task. When encoding items which can be
    /// dependencies (such as methods), this output should only be emitted in
    /// one Viper program.
    type OutputFullLocal<'vir>: Clone
    where
        Self: 'vir;

    /// Fully encoded output for this task for dependents. When encoding items
    /// which can be dependencies (such as methods), this output should be
    /// emitted in each Viper program that depends on this task.
    type OutputFullDependency<'vir>: Clone
        = ()
    where
        Self: 'vir;

    type EnqueueingError: Clone + std::fmt::Debug = ();
    type EncodingError: Clone + std::fmt::Debug;

    /// Enters the given function with a reference to the cache for this
    /// encoder.
    fn with_cache<'vir, F, R>(f: F) -> R
    where
        Self: 'vir,
        F: FnOnce(&'vir CacheRef<'vir, Self>) -> R;

    //fn get_all_outputs() -> Self::CacheRef<'vir> {
    //  todo!()
    //  // while ... { process() } // process items in the queue
    //  //Self::cache()
    //}

    fn enqueue<'vir>(task: Self::TaskDescription<'vir>)
    where
        Self: 'vir,
    {
        let task_key = Self::task_to_key(&task);
        let task_key_clone = task_key.clone(); // TODO: remove?

        if Self::with_cache(move |cache| cache.borrow().contains_key(&task_key_clone)) {
            return;
        }

        // enqueue, expecting no entry (we just checked)
        assert!(Self::with_cache(move |cache| cache
            .borrow_mut()
            .insert(task_key, TaskEncoderCacheState::Enqueued,)
            .is_none()));
    }

    fn encode_ref<'vir>(
        task: Self::TaskDescription<'vir>,
    ) -> Result<Self::OutputRef<'vir>, TaskEncoderError<Self>>
    where
        Self: 'vir,
    {
        let task_key = Self::task_to_key(&task);

        // is there an output ref available already?
        let task_key_clone = task_key.clone();
        if let Some(output_ref) =
            Self::with_cache(move |cache| match cache.borrow().get(&task_key_clone) {
                Some(TaskEncoderCacheState::Started { output_ref, .. })
                | Some(TaskEncoderCacheState::Encoded { output_ref, .. })
                | Some(TaskEncoderCacheState::ErrorEncode { output_ref, .. }) => {
                    Some(output_ref.clone())
                }
                _ => None,
            })
        {
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
        if let Some(output_ref) =
            Self::with_cache(move |cache| match cache.borrow().get(&task_key_clone) {
                Some(TaskEncoderCacheState::Started { output_ref, .. })
                | Some(TaskEncoderCacheState::Encoded { output_ref, .. })
                | Some(TaskEncoderCacheState::ErrorEncode { output_ref, .. }) => {
                    Some(output_ref.clone())
                }
                _ => None,
            })
        {
            return Ok(output_ref);
        }

        panic!("output ref not found after encoding") // TODO: error?
    }

    fn encode<'vir>(
        task: Self::TaskDescription<'vir>,
        need_output: bool,
    ) -> EncodeResult<'vir, Self>
    where
        Self: 'vir,
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
                    } => {
                        if need_output {
                            Some(Ok(Some((
                                output_ref.clone(),
                                output_local.clone(),
                                output_dep.clone(),
                            ))))
                        } else {
                            Some(Ok(None))
                        }
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

        let mut deps = TaskEncoderDependencies::new();
        let encode_result = Self::do_encode_full(&task_key, &mut deps);

        let output_ref = Self::with_cache(|cache| match cache.borrow().get(&task_key) {
            Some(
                TaskEncoderCacheState::Started { output_ref }
                | TaskEncoderCacheState::Encoded { output_ref, .. },
            ) => output_ref.clone(),
            _ => panic!("encoder did not provide output ref for task {task_key:?}"),
        });

        match encode_result {
            Ok((output_local, output_dep)) => {
                if need_output {
                    Self::with_cache(|cache| {
                        cache.borrow_mut().insert(
                            task_key,
                            TaskEncoderCacheState::Encoded {
                                output_ref: output_ref.clone(),
                                deps,
                                output_local: output_local.clone(),
                                output_dep: output_dep.clone(),
                            },
                        )
                    });
                    Ok(Some((output_ref, output_local, output_dep)))
                } else {
                    Self::with_cache(|cache| {
                        cache.borrow_mut().insert(
                            task_key,
                            TaskEncoderCacheState::Encoded {
                                output_ref,
                                deps,
                                output_local,
                                output_dep,
                            },
                        )
                    });
                    Ok(None)
                }
            }
            Err(EncodeFullError::AlreadyEncoded) => {
                Self::with_cache(|cache| match cache.borrow().get(&task_key).unwrap() {
                    TaskEncoderCacheState::Encoded {
                        output_ref,
                        output_local,
                        output_dep,
                        ..
                    } => {
                        if need_output {
                            Ok(Some((
                                // TODO: does it even make sense for an encoder to request the full encoding
                                //   when a cycle can occur?
                                output_ref.clone(),
                                output_local.clone(),
                                output_dep.clone(),
                            )))
                        } else {
                            Ok(None)
                        }
                    }
                    TaskEncoderCacheState::ErrorEnqueue { error }
                    | TaskEncoderCacheState::ErrorEncode { error, .. } => Err(error.clone()),
                    TaskEncoderCacheState::Started { .. } | TaskEncoderCacheState::Enqueued => {
                        panic!("encoder did not finish for task {task_key:?}")
                    }
                })
            }
            Err(EncodeFullError::DependencyError) => todo!(),
            Err(EncodeFullError::EncodingError(err, maybe_output_dep)) => {
                Self::with_cache(|cache| {
                    cache.borrow_mut().insert(
                        task_key,
                        TaskEncoderCacheState::ErrorEncode {
                            output_ref: output_ref.clone(),
                            deps,
                            error: TaskEncoderError::EncodingError(err.clone()),
                            output_dep: maybe_output_dep,
                        },
                    )
                });
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
    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir>;
    /*
        /// Given a task description, create a reference to the output.
        fn task_to_output_ref<'vir>(task: &Self::TaskDescription<'vir>) -> Self::OutputRef<'vir>;
    */
    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self>;

    fn all_outputs<'vir>() -> Vec<Self::OutputFullLocal<'vir>>
    where
        Self: 'vir,
    {
        Self::with_cache(|cache| {
            cache
                .borrow()
                .iter()
                .flat_map(|(_, cache_state)| {
                    if let TaskEncoderCacheState::Encoded { output_local, .. } = cache_state {
                        Some(output_local)
                    } else {
                        None
                    }
                })
                .cloned()
                .collect()
        })
    }
}
