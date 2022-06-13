pub enum Foo { }

impl Foo {
  pub fn do_thing(&self) -> Option<&i64> { //~ ERROR access to reference-typed fields is not supported
    return None
  }
}

fn main(){ }
