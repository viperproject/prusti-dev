pub mod clone;
pub mod convert;
pub mod default;
pub mod mem;
pub mod ops;
pub mod option;
pub mod result;
pub mod slice;

// NOTE: specs marked with FUTURE are not fully expressible yet (in a clean way).
// They are due to be revised later as features are added.

pub use clone::SnapshotEqualClone;
pub use convert::PureFrom;
pub use default::PureDefault;
pub use mem::KnownSize;
