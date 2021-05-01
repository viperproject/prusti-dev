use prusti_contracts::*;

struct ThreadRng;

fn thread_rng() -> ThreadRng {
    ThreadRng
}

struct RandWrapper {
    rng: ThreadRng
}

impl ThreadRng {
    #[trusted]
    fn gen_range(&self, min: u32, max: u32) -> u32 {
        unimplemented!();
    }
}

impl RandWrapper {
    #[trusted]
    #[ensures(result >= min && result < max)]
    pub fn gen_range(&mut self, min: u32, max: u32) -> u32 {
        self.rng.gen_range(min, max)
    }
}

#[ensures(result >= 0 && result < 10)]
fn func() -> u32{
    let mut rw = RandWrapper { rng: thread_rng() };
    rw.gen_range(0, 10)
}

fn main() {}
