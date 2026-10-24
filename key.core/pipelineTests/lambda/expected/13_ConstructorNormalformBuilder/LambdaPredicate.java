import java.util.Objects;

class LambdaPredicate {

    private final int test;

    public LambdaPredicate() {
        this.test = 1;
    }

    void m(int i) {
        int outer = 10;
        Predicate<Integer> tester = new Predicate__1();
        tester.test(outer);
    }

    @FunctionalInterface
    public interface Predicate<T> {

        boolean test(T var1);

        default Predicate<T> and(Predicate<? super T> var1) {
            Objects.requireNonNull(var1);
            return new Predicate__2(var1, this);
        }

        default Predicate<T> negate() {
            return new Predicate__3(this);
        }

        default Predicate<T> or(Predicate<? super T> var1) {
            Objects.requireNonNull(var1);
            return new Predicate__4(var1, this);
        }

        static <T> Predicate<T> isEqual(Object var0) {
            if (var0 == null) {
                return new Predicate__5();
            }
            return new Predicate__6(var0);
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

        public static Predicate $allocate();
    }

    private static final class Predicate__1 implements LambdaPredicate.Predicate<java.lang.Integer> {

        public boolean test(java.lang.Integer a) {
            return a > 10;
        }

        public Predicate__1() {
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

        public static Predicate__1 $allocate();

        public void $init() {
            super.$init();
        }
    }

    private static final class Predicate__2 implements LambdaPredicate.Predicate {

        public boolean test(java.lang.Object var2) {
            return outer_this_2.test(var2) && this._outer_final_var1.test(var2);
        }

        private final Predicate _outer_final_var1;

        private final Predicate outer_this_2;

        public Predicate__2(Predicate var1, Predicate outer_this_2) {
            this._outer_final_var1 = var1;
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

        public static Predicate__2 $allocate();

        public void $init(Predicate var1, Predicate outer_this_2) {
            super.$init();
            this._outer_final_var1 = var1;
            this.outer_this_2 = outer_this_2;
        }
    }

    private static final class Predicate__3 implements LambdaPredicate.Predicate {

        public boolean test(java.lang.Object var1) {
            return !outer_this_3.test(var1);
        }

        private final Predicate outer_this_3;

        public Predicate__3(Predicate outer_this_3) {
            this.outer_this_3 = outer_this_3;
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

        public static Predicate__3 $allocate();

        public void $init(Predicate outer_this_3) {
            super.$init();
            this.outer_this_3 = outer_this_3;
        }
    }

    private static final class Predicate__4 implements LambdaPredicate.Predicate {

        public boolean test(java.lang.Object var2) {
            return outer_this_4.test(var2) || this._outer_final_var1.test(var2);
        }

        private final Predicate _outer_final_var1;

        private final Predicate outer_this_4;

        public Predicate__4(Predicate var1, Predicate outer_this_4) {
            this._outer_final_var1 = var1;
            this.outer_this_4 = outer_this_4;
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

        public static Predicate__4 $allocate();

        public void $init(Predicate var1, Predicate outer_this_4) {
            super.$init();
            this._outer_final_var1 = var1;
            this.outer_this_4 = outer_this_4;
        }
    }

    private static final class Predicate__5 implements LambdaPredicate.Predicate {

        public boolean test(java.lang.Object var1) {
            return var1 == null;
        }

        public Predicate__5() {
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

        public static Predicate__5 $allocate();

        public void $init() {
            super.$init();
        }
    }

    private static final class Predicate__6 implements LambdaPredicate.Predicate {

        public boolean test(java.lang.Object var1) {
            return this._outer_final_var0.equals(var1);
        }

        private final Object _outer_final_var0;

        public Predicate__6(Object var0) {
            this._outer_final_var0 = var0;
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

        public static Predicate__6 $allocate();

        public void $init(Object var0) {
            super.$init();
            this._outer_final_var0 = var0;
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

    public static LambdaPredicate $allocate();

    public void $init() {
        super.$init();
        this.test = 1;
    }
}
