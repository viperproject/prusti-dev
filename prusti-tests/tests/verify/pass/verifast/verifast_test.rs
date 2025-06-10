extern crate prusti_contracts;

mod functions {
    use prusti_contracts::*;

    #[repr(C)]
    pub struct Point {
        pub x: i32,
        pub y: i32,
    }

    #[extern_spec(
        {file = "prusti-tests/tests/verify/pass/verifast/functions.c",}
        crate::functions)]
    extern "C" {
        #[ensures({translator = "verifast"}p.x == old(p.y))]
        #[ensures({translator = "verifast"}p.y == old(p.x))]
        pub fn swap(p: &mut Point);

        #[ensures({translator = "verifast"}p.x == old(p.y + p.x) && p.y == old(p.y - p.x) && result == p.x * p.y)]
        pub fn mangle(p: &mut Point) -> i32;

        #[ensures({translator = "verifast"}result == p.x * p.x + p.y * p.y)]
        pub fn squared_magnitude(p: &Point) -> i32;
    }

    extern "C" {
        pub fn swap(p: &mut Point);

        pub fn mangle(p: &mut Point) -> i32;

        pub fn squared_magnitude(p: &Point) -> i32;
    }
}

fn main() {
    use prusti_contracts::*;
    let x_val = 11;
    let y_val = 5;

    let mut p = functions::Point { x: x_val, y: y_val };

    unsafe {
        functions::swap(&mut p);
    }

    prusti_assert_eq!(p.x, y_val);
    prusti_assert_eq!(p.y, x_val);
    #[cfg(not(prusti))]
    {
        assert_eq!(p.x, y_val);
        assert_eq!(p.y, x_val);
    }

    let new_x_val = x_val + y_val;
    let new_y_val = x_val - y_val;
    let r_val = new_x_val * new_y_val;
    
    let r = unsafe {
        functions::mangle(&mut p)
    };
    
    prusti_assert_eq!(r, r_val);
    prusti_assert_eq!(p.x, new_x_val);
    prusti_assert_eq!(p.y, new_y_val);
    
    #[cfg(not(prusti))]
    {
        assert_eq!(r, r_val);
        assert_eq!(p.x, new_x_val);
        assert_eq!(p.y, new_y_val);
    }

    let p3 = functions::Point { x: 3, y: 4 };
    let r = unsafe {
        functions::squared_magnitude(&p3)
    };
    prusti_assert_eq!(r, 25);
    #[cfg(not(prusti))]
    {
        assert_eq!(r, 25);
    }
}
