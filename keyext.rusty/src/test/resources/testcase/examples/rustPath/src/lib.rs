#![feature(stmt_expr_attributes)]
#![feature(proc_macro_hygiene)]

extern crate rml_contracts;
use rml_contracts::*;

#[spec { name = "my_contract",
    requires(0 <= a && 0 <= b && a <= 100 && b <= 200),
    ensures(result == a + b)
    }]
pub fn add(a: u32, b: u32) -> u32 {
    a + b
}

// First verified function
#[spec {
    requires(a <= 1000 && b <= 1000),
    ensures(result == a * b)
    }]
pub fn mul(a: u64, mut b: u64) -> u64 {
    let mut n: u64 = 0;
    let old_b: u64 = b;
    #[invariant(n == a * (old_b - b) && b <= old_b)]
    #[variant(b)]
    loop {
        if b == 0 { break n; }
        n += a;
        b -= 1;
    }
}