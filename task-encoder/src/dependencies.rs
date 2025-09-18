use super::*;
use std::marker::PhantomData;

pub struct TaskEncoderDependencies<'vir, E: TaskEncoder + 'vir + ?Sized> {
    _marker: PhantomData<E>,
    task_key: Option<E::TaskKey<'vir>>,
    pub deps_local: Vec<&'vir dyn OutputRefAny>,
    pub deps_dep: Vec<&'vir dyn OutputRefAny>,
}

impl<'vir, E: TaskEncoder + 'vir + ?Sized> TaskEncoderDependencies<'vir, E> {
    pub(crate) fn new() -> Self {
        Self {
            _marker: PhantomData,
            task_key: None,
            deps_local: vec![],
            deps_dep: vec![],
        }
    }

    pub fn check_cycle(&self) -> Result<(), EncodeFullError<'vir, E>> {
        if let Some(task_key) = self.task_key.as_ref() {
            if E::with_cache(move |cache| {
                matches!(
                    cache.borrow().get(task_key),
                    Some(
                        TaskEncoderCacheState::ErrorEncode { .. }
                            | TaskEncoderCacheState::ErrorEnqueue { .. }
                    ),
                )
            }) {
                return Err(EncodeFullError::AlreadyEncoded);
            }
        }
        Ok(())
    }

    fn require_common<T, EOther: TaskEncoder>(
        &mut self,
        task: <EOther as TaskEncoder>::TaskDescription<'vir>,
        span: Option<Span>,
        res: Result<T, TaskEncoderError<EOther>>,
    ) -> Result<T, EncodeFullError<'vir, E>> {
        res
            .map_err(|err| EncodeFullError::DependencyError(vec![
                (EOther::ENCODER_NAME, EOther::describe_task(task), span.into_iter().collect()),
                (EOther::ENCODER_NAME, match err {
                    TaskEncoderError::EnqueueingError(_) => "? EnqueueingError".to_string(),
                    TaskEncoderError::EncodingError(err) => EOther::describe_error(err),
                    TaskEncoderError::DependencyError(_items) => "? DependencyError".to_string(),
                    TaskEncoderError::CyclicError => "? CyclicError".to_string(),
                }, Vec::new()),
            ]))
            .and_then(|result| {
                self.check_cycle()?;
                Ok(result)
            })
    }

    pub fn require_ref<EOther: TaskEncoder>(
        &mut self,
        task: <EOther as TaskEncoder>::TaskDescription<'vir>,
    ) -> Result<<EOther as TaskEncoder>::OutputRef<'vir>, EncodeFullError<'vir, E>> {
        self.require_common(task.clone(), None, EOther::encode_ref(task))
    }

    pub fn require_local<EOther: TaskEncoder + 'vir>(
        &mut self,
        task: <EOther as TaskEncoder>::TaskDescription<'vir>,
    ) -> Result<<EOther as TaskEncoder>::OutputFullLocal<'vir>, EncodeFullError<'vir, E>> {
        self.require_common(task.clone(), None, EOther::encode(task, true)
            .map(Option::unwrap)
            .map(|(_output_ref, output_local, _output_dep)| output_local))
    }

    pub fn require_dep<EOther: TaskEncoder + 'vir>(
        &mut self,
        task: <EOther as TaskEncoder>::TaskDescription<'vir>,
    ) -> Result<<EOther as TaskEncoder>::OutputFullDependency<'vir>, EncodeFullError<'vir, E>> {
        self.require_common(task.clone(), None, EOther::encode(task, true)
            .map(Option::unwrap)
            .map(|(_output_ref, _output_local, output_dep)| output_dep))
    }

    pub fn require_ref_spanned<EOther: TaskEncoder>(
        &mut self,
        task: <EOther as TaskEncoder>::TaskDescription<'vir>,
        span: Span,
    ) -> Result<<EOther as TaskEncoder>::OutputRef<'vir>, EncodeFullError<'vir, E>> {
        self.require_common(task.clone(), Some(span), EOther::encode_ref(task))
    }

    pub fn require_local_spanned<EOther: TaskEncoder + 'vir>(
        &mut self,
        task: <EOther as TaskEncoder>::TaskDescription<'vir>,
        span: Span,
    ) -> Result<<EOther as TaskEncoder>::OutputFullLocal<'vir>, EncodeFullError<'vir, E>> {
        self.require_common(task.clone(), Some(span), EOther::encode(task, true)
            .map(Option::unwrap)
            .map(|(_output_ref, output_local, _output_dep)| output_local))
    }

    pub fn require_dep_spanned<EOther: TaskEncoder + 'vir>(
        &mut self,
        task: <EOther as TaskEncoder>::TaskDescription<'vir>,
        span: Span,
    ) -> Result<<EOther as TaskEncoder>::OutputFullDependency<'vir>, EncodeFullError<'vir, E>> {
        self.require_common(task.clone(), Some(span), EOther::encode(task, true)
            .map(Option::unwrap)
            .map(|(_output_ref, _output_local, output_dep)| output_dep))
    }

    pub fn emit_output_ref(
        &mut self,
        task_key: E::TaskKey<'vir>,
        output_ref: E::OutputRef<'vir>,
    ) -> Result<(), EncodeFullError<'vir, E>> {
        assert!(
            self.task_key.replace(task_key.clone()).is_none(),
            "output ref already set for task key {task_key:?}"
        );
        self.check_cycle()?;
        assert!(E::with_cache(move |cache| matches!(
            cache
                .borrow_mut()
                .insert(task_key, TaskEncoderCacheState::Started { output_ref },),
            Some(TaskEncoderCacheState::Enqueued | TaskEncoderCacheState::Started { .. })
        )));
        Ok(())
    }
}
