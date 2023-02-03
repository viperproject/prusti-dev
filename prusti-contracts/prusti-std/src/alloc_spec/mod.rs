// These specs can't be built-in like the core specs since some no_std crates may not even have an allocator.
// Instead, prusti-std supports no_std through a feature.

pub mod string;
pub mod vec;
