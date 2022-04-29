//! Functions for axiomatizing generic ADTs. Allows registering constructors and
//! automatically derives destructors and injectivity axioms.

mod interface;

pub(super) use self::interface::{AdtsInterface, AdtsState};
