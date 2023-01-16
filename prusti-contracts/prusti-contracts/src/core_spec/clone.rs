use crate::*;

#[extern_spec]
trait Clone {
    #[refine_spec(where Self: SnapshotEqualClone, [
        ensures(result === self),
    ])]
    fn clone(&self) -> Self;
}

/// Specifies that `Clone::clone`, if implemented, preserves snapshot equality (`===`).
pub auto trait SnapshotEqualClone {}
