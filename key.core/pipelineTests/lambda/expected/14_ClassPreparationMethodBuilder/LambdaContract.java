class LambdaContract {

    interface IntFunction {

        int apply(int i);

        //@ model booleanpreCondition(inti);
        /*@ model */ boolean preCondition(int i);

        //@ model two_state booleanpostCondition(inti,int__result);
        /*@ model */ /*@ two_state */ boolean postCondition(int i, int __result);

        //@ model two_state booleaninvariantMethod(inti,int__result);
        /*@ model */ /*@ two_state */ boolean invariantMethod(int i, int __result);

        //@ model \locsetframeCondition(inti);
        /*@ model */ \locset frameCondition(int i);

        //@ model \locsetaccessibleMethod(inti);
        /*@ model */ \locset accessibleMethod(int i);

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

        public static IntFunction $allocate();

        static private void $clprepare() {
        }
    }

    int cap = 100;

    IntFunction clamp() {
        int min = 5;
        final int step = 2;
        return new IntFunction__1(step, min, this);
    }

    private static final class IntFunction__1 implements LambdaContract.IntFunction {

        public int apply(int x) {
            return x < (outer_this.cap + this._outer_final_step) ? (this._outer_final_min + x) : x;
        }

        private final int _outer_final_step;

        private final int _outer_final_min;

        private final LambdaContract outer_this;

        public IntFunction__1(int step, int min, LambdaContract outer_this) {
            this._outer_final_step = step;
            this._outer_final_min = min;
            this.outer_this = outer_this;
        }

        //@ model booleanpreCondition(intx){returnx [@18,46:47='>=',<235>,2:45] _outer_final_min && x [@26,71:72='>=',<235>,2:70] _outer_final_step;}
        /*@ model */ boolean preCondition(int x);

        //@ model two_state booleanpostCondition(intx,int__result){return__result [@25,78:79='<=',<240>,2:77] outer_this.cap [@31,96:96='+',<249>,2:95] _outer_final_step;}
        /*@ model */ /*@ two_state */ boolean postCondition(int x, int __result);

        //@ model two_state booleaninvariantMethod(intx,int__result){return__result [@25,80:81='>=',<235>,2:79] 0;}
        /*@ model */ /*@ two_state */ boolean invariantMethod(int x, int __result);

        //@ model \locsetframeCondition(intx){return\locset (\nothing);}
        /*@ model */ \locset frameCondition(int x);

        //@ model \locsetaccessibleMethod(intx){return\locset (outer_this.cap);}
        /*@ model */ \locset accessibleMethod(int x);

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

        public static IntFunction__1 $allocate();

        public void $init(int step, int min, LambdaContract outer_this) {
            super.$init();
            this._outer_final_step = step;
            this._outer_final_min = min;
            this.outer_this = outer_this;
        }

        static private void $clprepare() {
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

    public static LambdaContract $allocate();

    public LambdaContract() {
    }

    public void $init() {
        super.$init();
        this.cap = 100;
        super.$init();
        this.cap = 100;
    }

    static private void $clprepare() {
    }
}
