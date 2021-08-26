fn go(arg1: &str) -> &str {
    if arg1 == "f".to_string() {
       panic!(); //~^ ERROR panic!(..) statement might be reachable
    } 
    arg1
}

fn main() {
 go("bar");
}
