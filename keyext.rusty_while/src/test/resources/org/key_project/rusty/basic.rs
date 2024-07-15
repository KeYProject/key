fn f(a: i32, b: i32) -> i32 {
    let mut a: i32 = a + b;
    let b: i32 = a - b;
    a = a - b;
    a
}