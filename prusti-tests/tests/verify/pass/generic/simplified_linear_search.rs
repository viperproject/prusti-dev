use prusti_contracts::*;

pub struct VecWrapper<T> {
    v: Vec<T>,
}

impl<T: Eq> VecWrapper<T> {
    #[trusted]
    #[pure]
    pub fn len(&self) -> usize {
        self.v.len()
    }

    #[trusted]
    #[pure]
    pub fn present(&self, index: usize, value: &T) -> bool {
        self.v[index] == *value
    }
}

pub enum UsizeOption {
    Some(usize),
    None,
}

impl UsizeOption {
    #[pure]
    pub fn is_some(&self) -> bool {
        match self {
            UsizeOption::Some(_) => true,
            UsizeOption::None => false,
        }
    }
    #[pure]
    pub fn is_none(&self) -> bool {
        match self {
            UsizeOption::Some(_) => false,
            UsizeOption::None => true,
        }
    }
}

fn linear_search<T: Eq>(arr: &VecWrapper<T>, elem: &T) -> UsizeOption {
    let mut i = 0;
    let mut done = false;

    while i < arr.len() && !done {
        if arr.present(i, elem) {
            done = true;
        } else {
            i += 1;
        }
    }

    if done {
        UsizeOption::Some(i)
    } else {
        UsizeOption::None
    }
}

#[trusted]
fn main() {}
