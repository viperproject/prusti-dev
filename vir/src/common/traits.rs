use std::hash::Hasher;

pub trait HashWithPosition {
    fn hash<H: Hasher>(&self, state: &mut H);

    fn hash_slice<H: Hasher>(data: &[Self], state: &mut H)
    where
        Self: Sized,
    {
        for piece in data {
            piece.hash(state)
        }
    }
}

impl<T: HashWithPosition> HashWithPosition for Option<T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        let discriminant = core::mem::discriminant(self);
        ::core::hash::Hash::hash(&discriminant, state);
        if let Some(value) = self {
            HashWithPosition::hash(value, state);
        }
    }
}

impl<T: HashWithPosition> HashWithPosition for Vec<T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        for piece in self {
            HashWithPosition::hash(piece, state);
        }
    }
}

// impl HashWithPosition for crate::common::position::Position {
//     fn hash<H: Hasher>(&self, state: &mut H) {
//         core::hash::Hash::hash(self, state);
//     }
// }

macro delegate_hash_with_position($($t:ty),*) {
    $(
        impl HashWithPosition for $t {
            fn hash<H: Hasher>(&self, state: &mut H) {
                core::hash::Hash::hash(self, state);
            }
        }
    )*
}

delegate_hash_with_position! {
    bool,
    u8, u16, u32, u64, u128,
    i8, i16, i32, i64, i128,
    String,
    crate::common::position::Position
}
