use crate::*;

#[extern_spec]
trait Clone {
	#[ghost_constraint(Self: SnapshotEqualClone, [
		ensures(result === self),
	])]
	fn clone(&self) -> Self;
}

/// Specifies that `Clone::clone`, if implemented, preserves snapshot equality (`===`).
pub auto trait SnapshotEqualClone {}
