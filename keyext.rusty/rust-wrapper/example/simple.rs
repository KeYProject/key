#[allow(unused_mut, dead_code, unused_assignments)]
fn some_name(mut i: u32, mut b: bool) {
    {
        let x: &u32 = &i;
        let j: u32 = i;
        let y: &u32 = &j;
        b = x == y;
        b
    };
}
