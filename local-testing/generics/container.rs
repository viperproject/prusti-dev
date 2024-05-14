use prusti_contracts::*;

struct Container<T> {
    content: T,
}

#[requires(container.content == 123)]
#[ensures(result.content == 124)]
fn increment_container(container: Container<i32>) -> Container<i32> {
    Container { content: container.content + 1 }
}

#[ensures(result > 123)]
fn client() -> i32 {
    let num_container = Container { content: 123 };
    let incremented_container = increment_container(num_container);
    incremented_container.content
}

fn main(){}
