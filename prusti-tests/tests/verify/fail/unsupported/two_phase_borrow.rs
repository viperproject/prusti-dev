fn foo(a: &mut [i32], l: usize) {}
 
fn bar(a: &mut [i32]) {  //~ ERROR two-phase borrows are not supported
    foo(a, a.len());
}
 
fn main() {}
