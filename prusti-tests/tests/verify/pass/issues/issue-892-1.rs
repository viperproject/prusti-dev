use prusti_contracts::*;

fn main() {}

#[derive(Clone, Copy)]
pub enum Foo {
    Bar,
}

#[trusted]
#[ensures(match result {
    Ok(Some(r)) => r < 100,
    _ => true,
})]
pub fn foo() -> Result<Option<usize>, Foo> {
    unimplemented!()
}

pub fn test() -> Result<usize, Foo> {
    match foo() {
        Err(error) => Err(error),
        Ok(opt) => match opt {
            Some(res) => Ok(res),
            None => Err(Foo::Bar),
        },
    }
}
