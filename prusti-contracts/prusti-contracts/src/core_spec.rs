use crate::*;

#[extern_spec]
impl<T, E> ::core::result::Result<T, E> {
    #[pure]
    #[ensures(result == matches!(self, Ok(_)))]
    fn is_ok(&self) -> bool;

    #[pure]
    #[ensures(result == matches!(self, Err(_)))]
    fn is_err(&self) -> bool;
}

#[extern_spec]
impl<T, E: ::core::fmt::Debug> ::core::result::Result<T, E> {
    #[requires(matches!(self, Ok(_)))]
    fn unwrap(self) -> T;
}

// Crashes ☹
type Pointer<T> = *const T;
#[extern_spec]
impl<T> Pointer<T> {
    #[trusted]
    #[terminates]
    #[pure]
    // FIXME: This is needed because this function is special cased only in the
    // pure encoder and not in the impure one.
    #[ensures(result == self.is_null())]
    fn is_null(self) -> bool;
}

type MutPointer<T> = *mut T;
#[extern_spec]
impl<T> MutPointer<T> {
    #[trusted]
    #[terminates]
    #[pure]
    // FIXME: This is needed because this function is special cased only in the
    // pure encoder and not in the impure one.
    #[ensures(result == self.is_null())]
    fn is_null(self) -> bool;
}

#[extern_spec]
mod core {
    mod mem {
        use crate::*;

        #[pure]
        // FIXME: This is needed because this function is special cased only in the
        // pure encoder and not in the impure one.
        #[ensures(result == core::mem::size_of::<T>())]
        pub fn size_of<T>() -> usize;

        #[pure]
        // FIXME: What are the guarantees?
        // https://doc.rust-lang.org/std/mem/fn.align_of.html says nothing…
        #[ensures(result > 0)]
        // FIXME: This is needed because this function is special cased only in the
        // pure encoder and not in the impure one.
        #[ensures(result == core::mem::align_of::<T>())]
        pub fn align_of<T>() -> usize;
    }
}
