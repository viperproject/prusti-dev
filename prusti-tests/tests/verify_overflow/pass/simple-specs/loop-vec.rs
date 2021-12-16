use prusti_contracts::*;

struct VecWrapperPath{
    v: Vec<usize>
}

impl VecWrapperPath {
    #[trusted]
    pub fn new() -> Self {
        unimplemented!()
    }
}

fn find_path() -> Option<VecWrapperPath> {
    let mut result = None;
    while true {
        let path = VecWrapperPath::new();
        result = Some(path);
    }
    result
}

fn main() {}
