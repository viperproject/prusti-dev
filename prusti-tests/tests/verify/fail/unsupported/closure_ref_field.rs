pub struct Annotation {
    pub end: Option<i32>,
    pub fallback: i32
}

impl Annotation {
    fn ref_closure(self) -> i32 { //~ ERROR access to reference-typed fields is not supported
        self.end.as_ref().map_or(0, |value| {
            1
        })
    }
}

fn main() {

}
