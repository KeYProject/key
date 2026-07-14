public class EnumAnon {
    enum Op {
        ADD { int apply(int a, int b) { return a + b; } },
        SUB { int apply(int a, int b) { return a - b; } };
        abstract int apply(int a, int b);
    }
}
