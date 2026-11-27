class LambdaNested {

    private final int test;

    public LambdaNested() {
        this.test = 1;
    }

    void m(int i) {
        int outer = 10;
        final class MyFunctionalInterface__2 implements LambdaNested.MyFunctionalInterface {

            public int apply(int a) {
                final class MyFunctionalInterface__1 implements LambdaNested.MyFunctionalInterface {

                    public int apply(int x) {
                        return test * 2 + x;
                    }
                }
                MyFunctionalInterface g = new MyFunctionalInterface__1();
                return test + g.apply(a) * 2;
            }
        }
        make(new MyFunctionalInterface__2());
    }

    void make(MyFunctionalInterface f) {
        f.apply(10);
    }

    @java.lang.FunctionalInterface
    interface MyFunctionalInterface {

        public int apply(int i);
    }
}
