use prusti_contracts::*;

struct Nonsense {
    m2: u32, // multiple of 2
    m3: u32, // multiple of 3
    m5: u32, // multiple of 5
}

impl Nonsense {
    #[pure]
    fn valid(&self) -> bool {
        self.m2 % 2 == 0 && self.m3 % 3 == 0 && self.m5 % 5 == 0
    }

    #[requires(self.valid())]
    #[ensures(*result == old(self.m3))]
    #[assert_on_expiry(*result % 3 == 0, self.valid())] //~ ERROR might not hold
    fn m3_mut(&mut self) -> &mut u32 {
        &mut self.m5 // mistake
    }
}

#[requires(arg.valid())]
#[ensures(arg.valid())]
fn test(arg: &mut Nonsense) {
    let m3 = arg.m3_mut();
    *m3 += 3;
}

fn main() {}
