class A {
    int a;
    void test() {
        int u = 2;
        Function f = (x) -> {
                //@ ensures this.a+x != 23;
                int n = 2;
                return x+u+ this.a; };
    }

    interface Function {
        int apply(int x);
    }
}