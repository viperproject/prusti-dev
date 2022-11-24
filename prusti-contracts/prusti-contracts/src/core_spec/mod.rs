pub mod default;
pub mod option;
pub mod result;
pub mod clone;

// NOTE: specs marked with FUTURE are not fully expressible yet (in a clean way).
// They are due to be revised later as features are added.

pub use clone::SnapshotEqualClone;
pub use default::PureDefault;
