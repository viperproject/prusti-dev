extern crate prusti_contracts;

trait Foo {
    #[requires="-5 <= a && a <= 10"]
    #[requires="-25 <= b && b <= 30"]
    #[ensures="result.0 >= a"]
    #[ensures="result.1 >= b"]
    fn foo(&mut self, a: isize, b: isize) -> (isize, isize);
}

struct Dummy {
    d1: isize,
    d2: isize,
}

#[pure]
#[requires="a > std::isize::MIN"]
fn abs(a: isize) -> isize {
    if a < 0 { -a } else { a }
}

impl Foo for Dummy {
    #[ensures="result.0 < a"] //~ ERROR trait's precondition does not imply
    #[ensures="result.1 == 3"]
    #[ensures="self.d1 == a"]
    #[ensures="self.d2 == b"]
    fn foo(&mut self, a: isize, b: isize) -> (isize, isize) {
        let a = abs(a);
        let b = abs(b);
        self.d1 = a;
        self.d2 = b;
        (a - 1, 3)
    }
}


fn main() {}