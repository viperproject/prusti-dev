fn test() {
    loop {
        if let Some(_) = get_a_number() {
            1;
        } else {
            break;
        }
    }
}

fn get_a_number() -> Option<u32> {
    Some(5)
}

fn main() {}
