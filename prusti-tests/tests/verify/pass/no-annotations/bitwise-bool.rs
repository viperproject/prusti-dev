fn test_and() {
    assert!(true  & true  == true );
    assert!(true  & false == false);
    assert!(false & true  == false);
    assert!(false & false == false);
}

fn test_or() {
    assert!(true  | true  == true );
    assert!(true  | false == true );
    assert!(false | true  == true );
    assert!(false | false == false);
}

fn test_xor() {
    assert!(true  ^ true  == false);
    assert!(true  ^ false == true );
    assert!(false ^ true  == true );
    assert!(false ^ false == false);
}

fn main() {}
