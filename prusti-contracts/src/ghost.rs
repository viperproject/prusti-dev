use std::ops::*;
use core::marker::PhantomData;

pub unsafe auto trait Ghost {}

macro_rules! implement_ghost_type {
    ($ghost_type: ident) => {
        pub struct $ghost_type;
        unsafe impl Ghost for $ghost_type{}
    };
}

macro_rules! implement_ghost_type_generic {
    ($ghost_type: ident) => {
        pub struct $ghost_type<T: Ghost> {
            _type: PhantomData<T>
        }
        impl <T: Ghost> $ghost_type<T> {
            /// Constructor for generic ghost types.
            /// #Examples
            ///  ```rust
            ///  let seq_inst: GhostSeq<GhostInt> = GhostSeq::new();
            ///  ```
            pub fn new() -> Self {
                $ghost_type {
                    _type: PhantomData,
                }
            }
        }
        unsafe impl<T: Ghost> Ghost for $ghost_type<T> {}
    }
}

// Ghost variant of Viper type, Int
implement_ghost_type!(GhostInt);
// wrappers around standard operations on GhostInt
impl Add for GhostInt {
    type Output = Self;
    fn add(self, other: GhostInt) -> Self::Output {
        GhostInt
    }
}

impl Sub for GhostInt {
    type Output = Self;
    fn sub(self, other: GhostInt) -> Self::Output {
        GhostInt
    }
}

// Ghost variant of Viper type, Bool
implement_ghost_type!(GhostBool);
// wrappers around standard operations on GhostBool
impl BitAnd for GhostBool {
    type Output = Self;
    fn bitand(self, rhs: Self) -> Self::Output {
        GhostBool
    }
}

impl BitOr for GhostBool {
    type Output = Self;
    fn bitor(self, rhs: Self) -> Self::Output {
        GhostBool
    }
}

impl Not for GhostBool {
    type Output = Self;
    fn not(self) -> Self::Output {
        GhostBool
    }
}

// Ghost variant of Viper type, Seq[T]
implement_ghost_type_generic!(GhostSeq);
// wrappers around standard operations on GhostSeq
impl<T: Ghost> GhostSeq<T> {
    /// Push an item of type `T` to the ghost sequence
    /// #Examples
    /// ```rust
    /// let seq: GhostSeq<i32> = GhostSeq::new();
    /// seq.push(10);
    /// ```
    pub fn push(self, to_add: T) -> Self {
        GhostSeq::new()
    }

    /// Pop an item from a ghost sequence instance
    /// #Examples
    /// ```rust
    /// let seq: GhostSeq<i32> = GhostSeq::new();
    /// seq.push(10);
    /// seq.pop(10);
    /// ```
    pub fn pop(self, to_remove: T) -> Self {
        GhostSeq::new()
    }

    /// Concatenate two instances of ghost sequence
    /// #Examples
    /// ```rust
    /// let seq1: GhostSeq<i32> = GhostSeq::new();
    /// seq1.chain(seq2);
    /// ```
    pub fn chain(self, other: GhostSeq<T>) -> Self {
        GhostSeq::new()
    }
}

// Ghost variant of Viper type, Set[T]
implement_ghost_type_generic!(GhostSet);
// wrappers around standard operations on GhostSet
impl<T: Ghost> GhostSet<T> {
    pub fn push(self, to_add: T) -> Self {
        GhostSet::new()
    }

    pub fn remove(self, to_remove: T) -> Self {
        GhostSet::new()
    }

    pub fn union(self, other: GhostSeq<T>) -> Self {
        GhostSet::new()
    }

    pub fn intersection(self, other: GhostSeq<T>) -> Self {
        GhostSet::new()
    }
}

// Ghost variant of Viper type, MultiSet[T]
implement_ghost_type_generic!(GhostMultiSet);
// wrappers around standard operations on GhostMultiSet
impl<T: Ghost> GhostMultiSet<T> {
    pub fn push(self, to_add: T) -> Self {
        GhostMultiSet::new()
    }

    pub fn remove(self, to_remove: T) -> Self {
        GhostMultiSet::new()
    }

    pub fn union(self, other: GhostSeq<T>) -> Self {
        GhostMultiSet::new()
    }

    pub fn intersection(self, other: GhostSeq<T>) -> Self {
        GhostMultiSet::new()
    }

    pub fn has_element(self, element: T) -> GhostBool {
        GhostBool
    }
}
