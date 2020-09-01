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
    #[requires="-150 <= a && a <= 100"]
    #[requires="b > std::isize::MIN"]
    #[ensures="result.0 == abs(a)"]
    #[ensures="result.1 == abs(b)"]
    #[ensures="self.d1 == result.0"]
    #[ensures="self.d2 == result.1"]
    fn foo(&mut self, a: isize, b: isize) -> (isize, isize) {
        let a = abs(a);
        let b = abs(b);
        self.d1 = a;
        self.d2 = b;
        (a, b)
    }
}

impl Foo for () {
    fn foo(&mut self, a: isize, b: isize) -> (isize, isize) {
        (abs(a), abs(b))
    }
}

fn main() {}