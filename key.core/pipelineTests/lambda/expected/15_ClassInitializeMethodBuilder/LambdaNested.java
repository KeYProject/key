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

        @javax.annotation.processing.Generated()
        static private boolean $classInitializationInProgress;

        @javax.annotation.processing.Generated()
        static private boolean $classErroneous;

        @javax.annotation.processing.Generated()
        static private boolean $classInitialized;

        @javax.annotation.processing.Generated()
        static private boolean $classPrepared;

        @javax.annotation.processing.Generated()
        static public /*@ model */ boolean $staticInv;

        @javax.annotation.processing.Generated()
        static public /*@ model */ boolean $staticInv_free;

        public static MyFunctionalInterface $allocate();

        static private void $clprepare() {
        }

        static public void $clinit() {
            if (!@($classInitialized)) {
                if (!@($classInitializationInProgress)) {
                    if (!@($classPrepared)) {
                        //Created by ClassInitializeMethodBuilder.java:220
                        @($clprepare());
                    }
                    if (@($classErroneous)) {
                        throw new java.lang.NoClassDefFoundError();
                    }
                    //Created by ClassInitializeMethodBuilder.java:244
                    @($classInitializationInProgress) = true;
                    try {
                    }//Created by ClassInitializeMethodBuilder.java:195
                     catch (java.lang.Error err) {
                        //Created by ClassInitializeMethodBuilder.java:155
                        @($classInitializationInProgress) = false;
                        //Created by ClassInitializeMethodBuilder.java:156
                        @($classErroneous) = true;
                        throw err;
                    } catch (java.lang.Throwable twa) {
                        //Created by ClassInitializeMethodBuilder.java:155
                        @($classInitializationInProgress) = false;
                        //Created by ClassInitializeMethodBuilder.java:156
                        @($classErroneous) = true;
                        throw new java.lang.ExceptionInInitializerError(twa);
                    }
                    //Created by ClassInitializeMethodBuilder.java:250
                    @($classInitializationInProgress) = false;
                    //Created by ClassInitializeMethodBuilder.java:252
                    @($classErroneous) = false;
                    //Created by ClassInitializeMethodBuilder.java:254
                    @($classInitialized) = true;
                }
            }
        }
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

        @javax.annotation.processing.Generated()
        static private boolean $classInitializationInProgress;

        @javax.annotation.processing.Generated()
        static private boolean $classErroneous;

        @javax.annotation.processing.Generated()
        static private boolean $classInitialized;

        @javax.annotation.processing.Generated()
        static private boolean $classPrepared;

        @javax.annotation.processing.Generated()
        static public /*@ model */ boolean $staticInv;

        @javax.annotation.processing.Generated()
        static public /*@ model */ boolean $staticInv_free;

        public static MyFunctionalInterface__2 $allocate();

        public void $init(LambdaNested outer_this_2) {
            super.$init();
            this.outer_this_2 = outer_this_2;
        }

        static private void $clprepare() {
        }

        static public void $clinit() {
            if (!@($classInitialized)) {
                if (!@($classInitializationInProgress)) {
                    if (!@($classPrepared)) {
                        //Created by ClassInitializeMethodBuilder.java:220
                        @($clprepare());
                    }
                    if (@($classErroneous)) {
                        throw new java.lang.NoClassDefFoundError();
                    }
                    //Created by ClassInitializeMethodBuilder.java:244
                    @($classInitializationInProgress) = true;
                    try {
                        @(java.lang.Object.$clinit());
                    }//Created by ClassInitializeMethodBuilder.java:195
                     catch (java.lang.Error err) {
                        //Created by ClassInitializeMethodBuilder.java:155
                        @($classInitializationInProgress) = false;
                        //Created by ClassInitializeMethodBuilder.java:156
                        @($classErroneous) = true;
                        throw err;
                    } catch (java.lang.Throwable twa) {
                        //Created by ClassInitializeMethodBuilder.java:155
                        @($classInitializationInProgress) = false;
                        //Created by ClassInitializeMethodBuilder.java:156
                        @($classErroneous) = true;
                        throw new java.lang.ExceptionInInitializerError(twa);
                    }
                    //Created by ClassInitializeMethodBuilder.java:250
                    @($classInitializationInProgress) = false;
                    //Created by ClassInitializeMethodBuilder.java:252
                    @($classErroneous) = false;
                    //Created by ClassInitializeMethodBuilder.java:254
                    @($classInitialized) = true;
                }
            }
        }
    }

    @javax.annotation.processing.Generated()
    static private boolean $classInitializationInProgress;

    @javax.annotation.processing.Generated()
    static private boolean $classErroneous;

    @javax.annotation.processing.Generated()
    static private boolean $classInitialized;

    @javax.annotation.processing.Generated()
    static private boolean $classPrepared;

    @javax.annotation.processing.Generated()
    static public /*@ model */ boolean $staticInv;

    @javax.annotation.processing.Generated()
    static public /*@ model */ boolean $staticInv_free;

    public static LambdaNested $allocate();

    public void $init() {
        super.$init();
        this.test = 1;
    }

    static private void $clprepare() {
    }

    static public void $clinit() {
        if (!@($classInitialized)) {
            if (!@($classInitializationInProgress)) {
                if (!@($classPrepared)) {
                    //Created by ClassInitializeMethodBuilder.java:220
                    @($clprepare());
                }
                if (@($classErroneous)) {
                    throw new java.lang.NoClassDefFoundError();
                }
                //Created by ClassInitializeMethodBuilder.java:244
                @($classInitializationInProgress) = true;
                try {
                    @(java.lang.Object.$clinit());
                }//Created by ClassInitializeMethodBuilder.java:195
                 catch (java.lang.Error err) {
                    //Created by ClassInitializeMethodBuilder.java:155
                    @($classInitializationInProgress) = false;
                    //Created by ClassInitializeMethodBuilder.java:156
                    @($classErroneous) = true;
                    throw err;
                } catch (java.lang.Throwable twa) {
                    //Created by ClassInitializeMethodBuilder.java:155
                    @($classInitializationInProgress) = false;
                    //Created by ClassInitializeMethodBuilder.java:156
                    @($classErroneous) = true;
                    throw new java.lang.ExceptionInInitializerError(twa);
                }
                //Created by ClassInitializeMethodBuilder.java:250
                @($classInitializationInProgress) = false;
                //Created by ClassInitializeMethodBuilder.java:252
                @($classErroneous) = false;
                //Created by ClassInitializeMethodBuilder.java:254
                @($classInitialized) = true;
            }
        }
    }
}
