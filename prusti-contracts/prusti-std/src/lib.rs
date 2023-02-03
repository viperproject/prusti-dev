#![feature(allocator_api)] // to specify Vec
#![no_std] // disable std by default

// link to std if the feature is set
#[cfg(feature = "std")]
extern crate std;

// Even alloc can be disabled for consistency with std, and in preparation for future specs for other, possibly no_std, crates.
#[cfg(feature = "alloc")]
extern crate alloc;

// modules have a `_spec` suffix to avoid name conflicts with their crates.
#[cfg(feature = "alloc")]
pub mod alloc_spec;
#[cfg(feature = "std")]
pub mod std_spec;
