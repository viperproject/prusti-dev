// Testcase to check for constant tuples

const C: (i32, i32) = (0, 0);

fn main() {
    let _ = C.0;  //~ERROR the encoding of this reference copy has not been implemented
}
