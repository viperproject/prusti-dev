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
                        TaskEncoderCacheState::Encoded { .. }
                            | TaskEncoderCacheState::ErrorEncode { .. }
                            | TaskEncoderCacheState::ErrorEnqueue { .. }
                    ),
                )
            }) {
                return Err(EncodeFullError::AlreadyEncoded);
            }
        }
        Ok(())
    }

    pub fn require_ref<EOther: TaskEncoder>(
        &mut self,
        task: <EOther as TaskEncoder>::TaskDescription<'vir>,
    ) -> Result<<EOther as TaskEncoder>::OutputRef<'vir>, EncodeFullError<'vir, E>> {
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
    ) -> Result<<EOther as TaskEncoder>::OutputFullLocal<'vir>, EncodeFullError<'vir, E>> {
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
    ) -> Result<<EOther as TaskEncoder>::OutputFullDependency<'vir>, EncodeFullError<'vir, E>> {
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
