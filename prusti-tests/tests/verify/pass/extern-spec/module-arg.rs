use prusti_contracts::*;

fn main() {
    use module::inner::*;

    fn _trait_test_1<T: Example>() {
        assert!(T::example() == 42)
    }

    fn _trait_test_2<T: Advanced<U>, U: Copy>() {
        prusti_assert!(T::example() === T::example())
    }

    assert!(free_1() == 1);
    assert!(free_2() == 2);

    let s = Struct;
    assert!(s.method() == 42);
}

#[extern_spec(module::inner)]
trait Example {
    #[ensures(result == 42)]
    fn example() -> i32;
}

#[extern_spec(module::inner)]
trait Advanced<T>
where
    T: Copy,
{
    #[pure]
    fn example() -> T;
}

#[extern_spec(module)]
mod inner {
    #[ensures(result == 1)]
    fn free_1() -> i32;
}

#[extern_spec(module::inner)]
#[ensures(result == 2)]
fn free_2() -> i32;

#[extern_spec]
impl module::inner::Struct {
    #[ensures(result == 42)]
    fn method(&self) -> i32;
}

mod module {
    pub mod inner {
        pub trait Example {
            fn example() -> i32;
        }

        pub trait Advanced<T: Copy> {
            fn example() -> T;
        }

        pub fn free_1() -> i32 {
            1
        }

        pub fn free_2() -> i32 {
            2
        }

        pub struct Struct;

        impl Struct {
            pub fn method(&self) -> i32 {
                42
            }
        }
    }
}
