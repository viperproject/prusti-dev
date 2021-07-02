fn main() {
    println!("Hi");
    let mut t = [0];
    t[0] = 1;   //~ ERROR determining the region of array indexing is not supported
}