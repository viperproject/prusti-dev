pub struct Annotation {
    pub end: Option<i32>,
}

impl Annotation {
    fn encoded_len(self) -> usize { //~ ERROR access to reference-typed fields is not supported
        self.end.as_ref().map_or(0, |value| { //~ ERROR access to reference-typed fields in a closure is not supported
            1
        })
    }
}

fn main() {

}
