extern crate prusti_contracts;

fn test<'a>(x: &'a mut u32, y: &'a mut u32) -> &'a mut u32 {
	x
}

fn main() {}
