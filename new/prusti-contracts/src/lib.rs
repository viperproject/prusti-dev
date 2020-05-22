extern crate proc_macro;

#[cfg(any(prusti, feature = "prusti"))]
extern crate prusti_contracts_internal;

use proc_macro_hack::proc_macro_hack;

/// A macro for writing a precondition on a function.
pub use prusti_contracts_impl::requires;

/// A macro for writing a postcondition on a function.
pub use prusti_contracts_impl::ensures;

/// A macro for writing a loop invariant.
#[proc_macro_hack]
pub use prusti_contracts_impl::invariant;
