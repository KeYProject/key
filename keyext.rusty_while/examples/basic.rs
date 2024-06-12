fn f(a: i32, b: i32) -> (i32, i32) {
    let mut a = a + b;
    let b = a - b;
    a = a - b;
    (a, b)
}