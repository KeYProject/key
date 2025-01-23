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