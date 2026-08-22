class A {
    int a;
    void test() {
        int u = 2;
        u++;
        Function f = (x) -> {
            //@ ensures this.a+x != 23;
            return x+u+ this.a; };
    }

    interface Function {
        int apply(int x);
    }
}