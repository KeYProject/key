class LambdaNested {

    private final int test;

    public LambdaNested() {
        this.test = 1;
    }

    void m(int i) {
        int outer = 10;
        make(new MyFunctionalInterface__2(this));
    }

    void make(MyFunctionalInterface f) {
        f.apply(10);
    }

    @java.lang.FunctionalInterface
    interface MyFunctionalInterface {

        public int apply(int i);
    }

    private static final class MyFunctionalInterface__2 implements LambdaNested.MyFunctionalInterface {

        public int apply(int a) {
            MyFunctionalInterface g = new MyFunctionalInterface__1(outer_this_2);
            return outer_this_2.test + g.apply(a) * 2;
        }

        private static final class MyFunctionalInterface__1 implements LambdaNested.MyFunctionalInterface {

            public int apply(int x) {
                return outer_this.test * 2 + x;
            }

            private final LambdaNested outer_this;

            public MyFunctionalInterface__1(LambdaNested outer_this) {
                this.outer_this = outer_this;
            }
        }

        private final LambdaNested outer_this_2;

        public MyFunctionalInterface__2(LambdaNested outer_this_2) {
            this.outer_this_2 = outer_this_2;
        }
    }
}
