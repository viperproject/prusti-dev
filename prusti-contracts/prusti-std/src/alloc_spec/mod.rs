// In future, it might make sense to move these specs to yet another crate or have a feature to disable the std parts of this crate.
// alloc is usable in some no_std environments, so it would be helpful to support the use case of core + alloc without std.

pub mod string;
pub mod vec;
