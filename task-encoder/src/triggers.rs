use std::{cell::RefCell, collections::VecDeque};

use super::FxIndexMap;

use crate::TaskEncoder;

/// A queued trigger continuation. Stored as `'static` for the same reason as
/// the encoder caches (see `encoder_cache!`): the captured data lives in the
/// VIR arena, which outlives the drain.
pub(crate) type Continuation = Box<dyn FnOnce()>;

/// Continuations waiting for a task of encoder `E` to be requested.
type Watchers<'vir, E> = FxIndexMap<<E as TaskEncoder>::TaskKey<'vir>, Vec<Continuation>>;
pub type WatchersRef<'vir, E> = RefCell<Watchers<'vir, E>>;

type WatchersStatic<E> = FxIndexMap<<E as TaskEncoder>::TaskKey<'static>, Vec<Continuation>>;
pub type WatchersStaticRef<E> = RefCell<WatchersStatic<E>>;

thread_local! {
    static PENDING: RefCell<VecDeque<Continuation>> = RefCell::new(VecDeque::new());
}

/// Queues a continuation to run at the next [`drain_triggers`].
pub(crate) fn queue(f: Continuation) {
    PENDING.with(|pending| pending.borrow_mut().push_back(f));
}

pub(crate) fn mk_continuation<'vir>(f: impl FnOnce() + 'vir) -> Continuation {
    // SAFETY: `'vir` outlives the drain, as for the encoder caches (see the [`Continuation`] docs and `encoder_cache!`).
    unsafe { std::mem::transmute::<Box<dyn FnOnce() + 'vir>, Continuation>(Box::new(f)) }
}

/// Called when `key` first enters `E`'s cache: moves its waiting
/// continuations to the pending queue.
pub(crate) fn fire_watchers<'vir, E: TaskEncoder + 'vir + ?Sized>(key: &E::TaskKey<'vir>) {
    let fired = E::with_watchers(|watchers| watchers.borrow_mut().swap_remove(key));
    if let Some(fired) = fired {
        PENDING.with(|pending| pending.borrow_mut().extend(fired));
    }
}

/// Runs queued trigger continuations until quiescence. A continuation may
/// request new tasks, which can fire further triggers (or register new
/// ones), so this is a worklist fixpoint. Call once after the main encoding
/// phase, before outputs are emitted.
pub fn drain_triggers() {
    while let Some(f) = PENDING.with(|pending| pending.borrow_mut().pop_front()) {
        f();
    }
    debug_assert!(PENDING.with(|pending| pending.borrow().is_empty()));
}
