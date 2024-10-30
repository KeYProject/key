#[allow(unused_mut, dead_code, unused_assignments)]
fn some_name(mut i: u32, mut b: bool) {
    {
        let x = &i;
        let j = i;
        let y = &j;
        b = x == y;
        b
    };
}
