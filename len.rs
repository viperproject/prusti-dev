use prusti_contracts::*;

#[derive(Clone, Copy)]
pub enum Opt<T: Clone + Copy> {
    None,
    Some(T),
}

impl<T: Clone + Copy> Opt<T> {
    #[pure]
    pub fn is_none(&self) -> bool {
        match self {
            Opt::Some(_) => false,
            Opt::None => true,
        }
    }

    #[pure]
    pub fn is_some(&self) -> bool {
        !self.is_none()
    }

    #[pure]
    #[requires(self.is_some())]
    pub fn peek(&self) -> T {
        match self {
            Opt::Some(val) => *val,
            Opt::None => unreachable!(),
        }
    }
}

pub enum List<T> {
    Nil,

    #[allow(dead_code)]
    Cons(T, Box<List<T>>),
}

impl<T> List<T> {
    #[ensures(result.len() == 0_usize)]
    pub fn new() -> Self {
        let result = Self::Nil;

        // Prusti does not verify without these asserts
        assert!(result.len() == 0_usize);

        result
    }

    #[pure]
    #[trusted]
    #[ensures(result == (match self {
        List::Nil => 0,
        List::Cons(_, next) => 1 + next.len(),
    }))]
    pub fn len(&self) -> usize {
        match self {
            List::Nil => 0,
            List::Cons(_, next) => 1 + next.len(),
        }
    }
}

// Prusti does not verify without this function!
pub fn main() {
    let list: List<u8> = List::new();
    assert!(list.len() == 0);
}

// There are two quick and dirty ways to get around this if you just want a solution for now:
// - Disable overflow checking (the bad sln)
// - Mark your `len` function a `#[trusted]` and then program it into the postcondition (the better sln). Like so:
// ```
//     #[pure]
//     #[trusted]
//     #[ensures(result == (match self {
//         List::Nil => 0,
//         List::Cons(_, next) => 1 + next.len(),
//     }))]
//     pub fn len(&self) -> usize {
//         match self {
//             List::Nil => 0,
//             List::Cons(_, next) => 1 + next.len(),
//         }
//     }
// ```

// To actually solve this within Prusti, there are also two possibilities: