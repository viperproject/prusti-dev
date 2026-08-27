#![feature(rustc_private)]
#![feature(associated_type_defaults)]

use core::panic;
use prusti_rustc_interface::{data_structures::fx::FxIndexMap, span::Span};
use std::cell::RefCell;

mod cache;
mod dependencies;
mod result;
mod triggers;

pub use cache::*;
pub use dependencies::*;
pub use result::*;
pub use triggers::*;

#[derive(Debug, Default)]
pub struct Program<'vir> {
    fields: Vec<vir::FieldDyn<'vir>>,
    adts: Vec<vir::Adt<'vir>>,
    domains: Vec<vir::Domain<'vir>>,
    predicates: Vec<vir::Predicate<'vir>>,
    functions: Vec<vir::Function<'vir>>,
    methods: Vec<vir::Method<'vir>>,

    code: String,
    encoder_errors: Vec<(String, Span)>,
}

impl<'vir> Program<'vir> {
    pub fn header(&mut self, title: &str) {
        self.code.push_str("// -----------------------------\n");
        self.code.push_str(&format!("// {title}\n"));
        self.code.push_str("// -----------------------------\n");
    }

    pub fn add_field(&mut self, field: vir::FieldDyn<'vir>) {
        self.fields.push(field);
        self.code.push_str(&format!("{field:?}\n"));
    }

    pub fn add_adt(&mut self, adt: vir::Adt<'vir>) {
        self.adts.push(adt);
        self.code.push_str(&format!("{adt:?}\n"));
    }

    pub fn add_domain(&mut self, domain: vir::Domain<'vir>) {
        self.domains.push(domain);
        self.code.push_str(&format!("{domain:?}\n"));
    }

    pub fn add_predicate(&mut self, predicate: vir::Predicate<'vir>) {
        self.predicates.push(predicate);
        self.code.push_str(&format!("{predicate:?}\n"));
    }

    pub fn add_function(&mut self, function: vir::Function<'vir>) {
        self.functions.push(function);
        self.code.push_str(&format!("{function:?}\n"));
    }

    pub fn add_method(&mut self, method: vir::Method<'vir>) {
        self.methods.push(method);
        self.code.push_str(&format!("{method:?}\n"));
    }

    pub fn code(&self) -> &str {
        &self.code
    }

    pub fn mk_program(self) -> vir::Program<'vir> {
        vir::with_vcx(|vcx| {
            vcx.mk_program(
                vcx.alloc_slice(&self.fields),
                vcx.alloc_slice(&self.adts),
                vcx.alloc_slice(&self.domains),
                vcx.alloc_slice(&self.predicates),
                vcx.alloc_slice(&self.functions),
                vcx.alloc_slice(&self.methods),
            )
        })
    }

    pub fn encoder_errors(&mut self) -> &mut Vec<(String, Span)> {
        &mut self.encoder_errors
    }
}

#[derive(Debug, Clone, Copy)]
pub enum NeverError {}

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
    type OutputRef<'vir>: Clone + std::fmt::Debug + OutputRefAny
        = ()
    where
        Self: 'vir;

    /// Fully encoded output for this task. When encoding items which can be
    /// dependencies (such as methods), this output should only be emitted in
    /// one Viper program.
    type OutputFullLocal<'vir>: Clone
        = ()
    where
        Self: 'vir;

    /// Fully encoded output for this task for dependents. When encoding items
    /// which can be dependencies (such as methods), this output should be
    /// emitted in each Viper program that depends on this task.
    type OutputFullDependency<'vir>: Clone
        = ()
    where
        Self: 'vir;

    type EnqueueingError: Clone + std::fmt::Debug = NeverError;
    type EncodingError: Clone + std::fmt::Debug = NeverError;

    /// User-presentable name of this encoder.
    const ENCODER_NAME: &'static str;

    fn describe_task<'vir>(task: Self::TaskDescription<'vir>) -> String {
        format!("{task:?}")
    }

    fn describe_error(error: Self::EncodingError) -> String {
        format!("{error:?}")
    }

    /// Enters the given function with a reference to the cache for this
    /// encoder.
    fn with_cache<'vir, F, R>(f: F) -> R
    where
        Self: 'vir,
        F: FnOnce(&'vir CacheRef<'vir, Self>) -> R;

    /// Enters the given function with a reference to the trigger watchers for
    /// this encoder. These are continuations registered via [`Self::on_task_requested`],
    /// waiting for a task of this encoder to be requested.
    fn with_watchers<'vir, F, R>(f: F) -> R
    where
        Self: 'vir,
        F: FnOnce(&'vir WatchersRef<'vir, Self>) -> R;

    /// Queues `f` to run in [`drain_triggers`] once the given task of this
    /// encoder has been requested (enqueued, started, or encoded - not
    /// necessarily successfully). If it already has been, `f` is queued
    /// immediately. Continuations of tasks that are never requested do not
    /// run.
    ///
    /// Triggers must be registered during the encoding phase:
    /// [`drain_triggers`] runs before outputs are emitted, so continuations
    /// registered during `emit_outputs` would never run. From within an
    /// in-flight encoder that already knows the task is needed, use a plain
    /// `deps.require_*` instead.
    fn on_task_requested<'vir>(key: Self::TaskKey<'vir>, f: impl FnOnce() + 'vir)
    where
        Self: Sized + 'vir,
    {
        let f = mk_continuation(f);
        let requested = Self::with_cache(|cache| cache.borrow().contains_key(&key));
        if requested {
            triggers::queue(f);
        } else {
            Self::with_watchers(move |watchers| {
                watchers.borrow_mut().entry(key).or_default().push(f)
            });
        }
    }

    /// Queues `f` to run once *every* task in `keys` has been requested (the
    /// conjunction of [`Self::on_task_requested`]). An empty `keys` runs `f`
    /// unconditionally.
    fn on_all_requested<'vir>(mut keys: Vec<Self::TaskKey<'vir>>, f: impl FnOnce() + 'vir)
    where
        Self: Sized + 'vir,
    {
        match keys.pop() {
            None => queue(mk_continuation(f)),
            Some(key) => Self::on_task_requested(key, move || Self::on_all_requested(keys, f)),
        }
    }

    /// Queues `f` to run once *any* task in `keys` has been requested (the
    /// disjunction of [`Self::on_task_requested`]). `f` runs at most once, on
    /// the first such task; an empty `keys` never runs `f`.
    fn on_any_requested<'vir>(keys: Vec<Self::TaskKey<'vir>>, f: impl FnOnce() + 'vir)
    where
        Self: Sized + 'vir,
    {
        // The continuations share ownership of `f` and race to take it, so that
        // it runs exactly once regardless of how many keys become requested.
        let slot: std::rc::Rc<std::cell::Cell<Option<triggers::Continuation>>> =
            std::rc::Rc::new(std::cell::Cell::new(Some(mk_continuation(f))));
        for key in keys {
            let slot = slot.clone();
            Self::on_task_requested(key, move || {
                if let Some(f) = slot.take() {
                    f();
                }
            });
        }
    }

    //fn get_all_outputs() -> Self::CacheRef<'vir> {
    //  todo!()
    //  // while ... { process() } // process items in the queue
    //  //Self::cache()
    //}

    /*
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
        triggers::fire_watchers::<Self>(&task_key);
        let old = Self::with_cache(move |cache| {
            let v = TaskEncoderCacheState::Enqueued;
            cache.borrow_mut().insert(task_key, v)
        });
        assert!(old.is_none());
    }
    */

    fn encode_ref<'vir>(
        task: Self::TaskDescription<'vir>,
        span: Span,
    ) -> Result<Self::OutputRef<'vir>, TaskEncoderError<Self>>
    where
        Self: 'vir,
    {
        let task_key = Self::task_to_key(&task);

        // is there an output ref available already?
        let task_key_clone = task_key.clone();
        if let Some(output_ref) =
            Self::with_cache(move |cache| match cache.borrow().get(&task_key_clone) {
                Some(TaskEncoderCacheState::Started { output_ref })
                | Some(TaskEncoderCacheState::Restarted { output_ref })
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
        // even if the encoding was started previously, i.e. if the same task
        // was (recursively) requested from the same encoder before its first
        // invocation reached a call to `emit_output_ref` (see
        // `TaskEncoderCacheState::Encoding`).
        let encode_res = Self::encode(task, false, span);
        match encode_res {
            Ok(_) | Err(TaskEncoderError::DependencyError(..)) => (), // pass, check for output ref
            Err(err) => return Err(err),
        }

        let task_key_clone = task_key.clone();
        if let Some(output_ref) =
            Self::with_cache(move |cache| match cache.borrow().get(&task_key_clone) {
                Some(TaskEncoderCacheState::Started { output_ref })
                | Some(TaskEncoderCacheState::Restarted { output_ref })
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
        span: Span,
    ) -> EncodeResult<'vir, Self>
    where
        Self: 'vir,
    {
        let task_key = Self::task_to_key(&task);

        let in_cache = Self::with_cache(|cache| {
            let mut cache = cache.borrow_mut();

            let new_state = match cache.get(&task_key) {
                Some(
                    TaskEncoderCacheState::ErrorEnqueue { error, .. }
                    | TaskEncoderCacheState::ErrorEncode { error, .. },
                ) => return Some(Err(error.clone())),
                Some(TaskEncoderCacheState::Encoded {
                    output_ref,
                    output_local,
                    output_dep,
                    ..
                }) => {
                    return if need_output {
                        Some(Ok(Some((
                            output_ref.clone(),
                            output_local.clone(),
                            output_dep.clone(),
                        ))))
                    } else {
                        Some(Ok(None))
                    };
                }
                // A re-run is already in progress; another one could not make
                // progress over it (see `TaskEncoderCacheState`).
                Some(
                    TaskEncoderCacheState::ReEncoding | TaskEncoderCacheState::Restarted { .. },
                ) => return Some(Err(TaskEncoderError::CyclicError)),
                // Start the first run.
                None => {
                    triggers::fire_watchers::<Self>(&task_key);
                    TaskEncoderCacheState::Encoding
                }
                // In progress: re-run the encoding (see
                // `TaskEncoderCacheState::Started`).
                Some(TaskEncoderCacheState::Encoding) => TaskEncoderCacheState::ReEncoding,
                Some(TaskEncoderCacheState::Started { output_ref }) => {
                    TaskEncoderCacheState::Restarted {
                        output_ref: output_ref.clone(),
                    }
                }
            };
            cache.insert(task_key.clone(), new_state);
            None
        });
        if let Some(in_cache) = in_cache {
            return in_cache;
        }

        let value = task_key.clone();
        // The span stack is isolated across the encoder-context boundary: the
        // encoding is demand-driven and cached, so its spans must not chain
        // up to whatever span is ambient at the (first) demand site.
        let catch_result = vir::with_vcx(|vcx| {
            vcx.with_span_stack_isolated(|| {
                std::panic::catch_unwind(std::panic::AssertUnwindSafe(move || {
                    let mut deps = TaskEncoderDependencies::new();
                    let encode_result = Self::do_encode_full(&value, &mut deps);
                    (encode_result, deps)
                }))
            })
        });

        let (encode_result, deps) = catch_result.map_err(|panic_payload| {
            // There was a panic within the encoder. We want to report it
            // and return an error to the caller.
            let msg = if let Some(s) = panic_payload.downcast_ref::<&str>() {
                s.to_string()
            } else if let Some(s) = panic_payload.downcast_ref::<String>() {
                s.clone()
            } else {
                "<unknown panic>".to_string()
            };
            let error = TaskEncoderError::PanicError(msg);
            Self::with_cache(|cache| {
                let mut cache = cache.borrow_mut();
                match cache.get(&task_key) {
                    Some(
                        TaskEncoderCacheState::Started { output_ref }
                        | TaskEncoderCacheState::Restarted { output_ref },
                    ) => {
                        let output_ref = output_ref.clone();
                        cache.insert(
                            task_key.clone(),
                            TaskEncoderCacheState::ErrorEncode {
                                output_ref,
                                deps: TaskEncoderDependencies::new(),
                                error: error.clone(),
                                output_dep: None,
                                spans: vec![span],
                            },
                        );
                    }
                    _ => {
                        cache.insert(
                            task_key.clone(),
                            TaskEncoderCacheState::ErrorEnqueue {
                                error: error.clone(),
                                spans: vec![span],
                            },
                        );
                    }
                }
            });
            error
        })?;

        // `ErrorEncode`: a suspended run whose re-run failed (moving the task
        // to that state) finds its own error here.
        let output_ref = Self::with_cache(|cache| match cache.borrow().get(&task_key) {
            Some(
                TaskEncoderCacheState::Started { output_ref }
                | TaskEncoderCacheState::Restarted { output_ref }
                | TaskEncoderCacheState::Encoded { output_ref, .. }
                | TaskEncoderCacheState::ErrorEncode { output_ref, .. },
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
                    TaskEncoderCacheState::ErrorEnqueue { error, .. }
                    | TaskEncoderCacheState::ErrorEncode { error, .. } => Err(error.clone()),
                    TaskEncoderCacheState::Encoding
                    | TaskEncoderCacheState::ReEncoding
                    | TaskEncoderCacheState::Started { .. }
                    | TaskEncoderCacheState::Restarted { .. } => {
                        panic!("encoder did not finish for task {task_key:?}")
                    }
                })
            }
            Err(EncodeFullError::DependencyError(stack)) => {
                let owned_stack =
                    std::iter::once((Self::ENCODER_NAME, Self::describe_task(task), Vec::new()))
                        .chain(
                            stack
                                .into_iter()
                                .map(|(encoder, task, spans)| (encoder, task, spans.clone())),
                        )
                        .collect::<Vec<_>>();
                Self::with_cache(|cache| {
                    cache.borrow_mut().insert(
                        task_key,
                        TaskEncoderCacheState::ErrorEncode {
                            output_ref: output_ref.clone(),
                            deps,
                            error: TaskEncoderError::DependencyError(owned_stack.clone()),
                            output_dep: None,
                            spans: vec![span],
                        },
                    )
                });
                Err(TaskEncoderError::DependencyError(owned_stack))
            }
            Err(EncodeFullError::EncodingError(err, maybe_output_dep)) => {
                Self::with_cache(|cache| {
                    cache.borrow_mut().insert(
                        task_key,
                        TaskEncoderCacheState::ErrorEncode {
                            output_ref: output_ref.clone(),
                            deps,
                            error: TaskEncoderError::EncodingError(err.clone()),
                            output_dep: maybe_output_dep,
                            spans: vec![span],
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

    fn all_outputs_local_no_errors<'vir>(
        program: &mut Program<'vir>,
    ) -> Vec<Self::OutputFullLocal<'vir>>
    where
        Self: 'vir,
    {
        let (outputs, errored) = Self::all_outputs_local();
        for (key, error, spans) in errored {
            let span = spans
                .into_iter()
                .next()
                .unwrap_or(prusti_rustc_interface::span::DUMMY_SP);
            let msg = match error {
                TaskEncoderError::EncodingError(err) => Self::describe_error(err),
                other => format!(
                    "encoder '{}' failed to encode {:?}:\n {:?}",
                    Self::ENCODER_NAME,
                    key,
                    other
                ),
            };
            program.encoder_errors.push((msg, span));
        }
        outputs
    }

    #[allow(clippy::type_complexity)]
    fn all_outputs_local<'vir>() -> (
        Vec<Self::OutputFullLocal<'vir>>,
        Vec<(Self::TaskKey<'vir>, TaskEncoderError<Self>, Vec<Span>)>,
    )
    where
        Self: 'vir,
    {
        Self::with_cache(|cache| {
            let mut outputs = Vec::new();
            let mut errored = Vec::new();
            for (key, cache_state) in cache.borrow().iter() {
                match cache_state {
                    TaskEncoderCacheState::Encoded { output_local, .. } => {
                        outputs.push(output_local.clone());
                    }
                    TaskEncoderCacheState::ErrorEncode { error, spans, .. }
                    | TaskEncoderCacheState::ErrorEnqueue { error, spans } => {
                        errored.push((key.clone(), error.clone(), spans.clone()));
                    }
                    _ => panic!("task encoder not completed: {key:?}"),
                }
            }
            (outputs, errored)
        })
    }

    fn emit_outputs<'vir>(_program: &mut Program<'vir>) {}
}
