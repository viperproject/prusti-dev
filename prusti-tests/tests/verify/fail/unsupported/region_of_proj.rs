fn main() {
    println!("Hi");
    let mut t = [0];
    t[0] = 1;   //~ ERROR determining the region of projection Index(_14) is not supported
}