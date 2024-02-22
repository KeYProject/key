// verbose: true
// broken: false
// msgContains: Method f(\bigint) not found
// position: 10/20

class BigInt {

    static int f(int x) { return 42; }

    //@ invariant f(3+4) == 42;
}
