use prusti_contracts::*;

pub struct Wrapper(u32);

impl Wrapper {
    #[pure]
    pub fn get(&self) -> u32 {
        self.0
    }

}

fn capitalize(vec: &mut Wrapper) {
    while true {
        body_invariant!(vec.get() == old(vec.get()));
    }
}

fn main(){
}
