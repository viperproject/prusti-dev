use prusti_contracts::*;

pub struct T{}

impl T {

    #[trusted]
    #[pure]
    pub fn read(&self) -> bool {
        false
    }

    #[trusted]
    pub fn modify(&mut self) {
    }
}

fn test1(x: &mut T) {
    let mut continue_loop_1 = true;
    while continue_loop_1 {
        let mut continue_loop_2 = true;
        while continue_loop_2 {
            continue_loop_2 = x.read();
        }
        let z = &mut *x;
        continue_loop_1 = false;
    }
}

fn test2(x: &mut T) {
    let mut continue_loop_1 = true;
    while continue_loop_1 {
        let mut continue_loop_2 = true;
        while continue_loop_2 {
            continue_loop_2 = x.read();
        }
        x.modify();
        continue_loop_1 = false;
    }
}

fn main() {
}
