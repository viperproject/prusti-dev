struct Node<T> {
    f: T,
    n: Option<Box<Node<T>>>,
}

fn foo<'a, T>(a: &'a T, b: &'a T, c: &'a T) -> Node<&'a T> {
    
}