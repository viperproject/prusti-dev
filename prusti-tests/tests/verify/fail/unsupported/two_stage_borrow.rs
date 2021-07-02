fn foo(a: &mut [i32], l: usize) {}
 
fn bar(a: &mut [i32]) {  //~ ERROR two stage borrow is not supported
    foo(a, a.len());
}
 
fn main() {}