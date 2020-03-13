extern crate prusti_contracts;

trait Foo {
    #[requires="-5 <= a && a <= 10"] //~ ERROR does not imply trait's postcondition
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
    #[requires="-1 <= a && a <= 1"]
    #[requires="b == 0"]
    fn foo(&mut self, a: isize, b: isize) -> (isize, isize) {
        let a = abs(a);
        let b = abs(b);
        self.d1 = a;
        self.d2 = b;
        (a, b)
    }
}


fn main() {}