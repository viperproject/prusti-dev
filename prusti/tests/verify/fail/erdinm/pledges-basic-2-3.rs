extern crate prusti_contracts;

struct Nonsense {
    m2: i32, // multiple of 2
    m3: i32, // multiple of 3
    m5: i32, // multiple of 5
}

impl Nonsense {
    #[pure]
    fn valid(&self) -> bool {
        self.m2 % 2 == 0 && self.m3 % 3 == 0 && self.m5 % 5 == 0
    }

    #[requires="self.valid()"]
    #[ensures="*result == old(self.m3)"]
    #[ensures="assert_on_expiry(
        true,
        self.valid()
    )"]
    fn m3_mut(&mut self) -> &mut i32 { //~ ERROR pledge in the postcondition might not hold
        &mut self.m3
    }
}

#[requires="arg.valid()"]
#[ensures="arg.valid()"]
fn test(arg: &mut Nonsense) {
    let m3 = arg.m3_mut();
    *m3 += 3;
}

fn main() {}
