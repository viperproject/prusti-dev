pub mod clone;
pub mod default;
pub mod mem;
pub mod ops;
pub mod option;
pub mod result;

// NOTE: specs marked with FUTURE are not fully expressible yet (in a clean way).
// They are due to be revised later as features are added.

pub use clone::SnapshotEqualClone;
pub use default::PureDefault;
