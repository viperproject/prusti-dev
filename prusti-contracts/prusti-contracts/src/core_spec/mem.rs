use crate::*;

#[extern_spec]
mod core {
    mod mem {
        use crate::*;

        #[pure]
        #[ghost_constraint(T: core_spec::mem::KnownSize, [ensures(result == T::size())])]
        fn size_of<T>() -> usize;

        #[pure]
        #[ghost_constraint(T: core_spec::mem::KnownSize, [ensures(result == T::align())])]
        fn align_of<T>() -> usize;

        #[ensures(*x === old(snap(y)) && *y === old(snap(x)))]
        fn swap<T>(x: &mut T, y: &mut T);
    }
}

pub trait KnownSize {
    #[pure]
    fn size() -> usize;

    #[pure]
    fn align() -> usize;
}

macro_rules! known_size_spec {
    ($t:ty, $size:expr, $align:expr) => {
        #[refine_trait_spec]
        impl KnownSize for $t {
            #[pure]
            fn size() -> usize {
                $size
            }

            #[pure]
            fn align() -> usize {
                $align
            }
        }
    };
    ($t:ty, $size:expr) => {
		known_size_spec!($t, $size, $size);
	};
}

known_size_spec!(bool, 1);

known_size_spec!(i8, 1);
known_size_spec!(i16, 2);
known_size_spec!(i32, 4);
known_size_spec!(i64, 8);
known_size_spec!(i128, 16);

known_size_spec!(u8, 1);
known_size_spec!(u16, 2);
known_size_spec!(u32, 4);
known_size_spec!(u64, 8);
known_size_spec!(u128, 16);

known_size_spec!(f32, 4);
known_size_spec!(f64, 8);

#[cfg(target_pointer_width = "16")]
known_size_spec!(usize, 2);
#[cfg(target_pointer_width = "16")]
known_size_spec!(isize, 2);

#[cfg(target_pointer_width = "32")]
known_size_spec!(usize, 4);
#[cfg(target_pointer_width = "32")]
known_size_spec!(isize, 4);

#[cfg(target_pointer_width = "64")]
known_size_spec!(usize, 8);
#[cfg(target_pointer_width = "64")]
known_size_spec!(isize, 8);
