class LambdaGeneric {

    private final int test;

    public LambdaGeneric() {
        this.test = 1;
    }

    void m(int i) {
        int outer = 10;
        make(new MyFunctionalInterface__2(this));
    }

    void make(MyFunctionalInterface<Integer> f) {
        f.apply(10);
    }

    @java.lang.FunctionalInterface
    interface MyFunctionalInterface<T> {

        public boolean apply(T i);
    }

    private static final class MyFunctionalInterface__2 implements LambdaGeneric.MyFunctionalInterface<java.lang.Integer> {

        public boolean apply(java.lang.Integer a) {
            MyFunctionalInterface<Integer> g = new MyFunctionalInterface__1(outer_this_2);
            return g.apply(a) && a > 2;
        }

        private static final class MyFunctionalInterface__1 implements LambdaGeneric.MyFunctionalInterface<java.lang.Integer> {

            public boolean apply(java.lang.Integer x) {
                return (outer_this.test * 2 + x) > 0;
            }

            private final LambdaGeneric outer_this;

            public MyFunctionalInterface__1(LambdaGeneric outer_this) {
                this.outer_this = outer_this;
            }
        }

        private final LambdaGeneric outer_this_2;

        public MyFunctionalInterface__2(LambdaGeneric outer_this_2) {
            this.outer_this_2 = outer_this_2;
        }
    }
}
