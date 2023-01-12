use prusti_contracts::*;

#[extern_spec]
impl<T> Option<T> {
    #[pure]
    fn is_some(&self) -> bool {} //~ ERROR: Unexpected method body. (Extern specs only define specifications.)
}

#[extern_spec]
trait Clone {
    #[pure]
    fn clone(&self) -> Self {} //~ ERROR: Unexpected method body. (Extern specs only define specifications.)
}

#[extern_spec]
impl Clone for i32 {
    #[pure]
    fn clone(&self) -> Self {} //~ ERROR: Unexpected method body. (Extern specs only define specifications.)
}

#[extern_spec]
mod core {
    mod mem {
        #[pure]
        pub fn size_of<T>() -> usize {} //~ ERROR: Unexpected method body. (Extern specs only define specifications.)
    }
}
