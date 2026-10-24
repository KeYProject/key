class LambdaGeneric {

    private final int test;

    public LambdaGeneric() {
        this.test = 1;
    }

    void m(int i) {
        int outer = 10;
        final class MyFunctionalInterface__2 implements LambdaGeneric.MyFunctionalInterface<java.lang.Integer> {

            public boolean apply(java.lang.Integer a) {
                final class MyFunctionalInterface__1 implements LambdaGeneric.MyFunctionalInterface<java.lang.Integer> {

                    public boolean apply(java.lang.Integer x) {
                        return (test * 2 + x) > 0;
                    }
                }
                MyFunctionalInterface<Integer> g = new MyFunctionalInterface__1();
                return g.apply(a) && a > 2;
            }
        }
        make(new MyFunctionalInterface__2());
    }

    void make(MyFunctionalInterface<Integer> f) {
        f.apply(10);
    }

    @java.lang.FunctionalInterface
    interface MyFunctionalInterface<T> {

        public boolean apply(T i);
    }
}
