/**
 * Side-effectful lambda expressions (Csiky's thesis, Sec. 6.4): the frame is stated as the
 * model fields {@code footprint}/{@code accessibleFields} of the functional interface, so the
 * conversion (Def. 7, Table 6.1) produces {@code model} fields with {@code represents}
 * clauses instead of {@code frameCondition}/{@code accessibleMethod} methods. The invariant
 * clause of a side-effectful lambda is converted into {@code invariantMethod} taking the
 * result of the functional method.
 */
class LambdaSideEffect {

    interface Counter {

        int apply(int i);

        /*@ model */ \locset footprint;

        /*@ model */ \locset accessibleFields;

        //@ model booleanpreCondition(inti);
        /*@ model */ boolean preCondition(int i);

        //@ model two_state booleanpostCondition(inti,int__result);
        /*@ model */ /*@ two_state */ boolean postCondition(int i, int __result);

        //@ model two_state booleaninvariantMethod(inti,int__result);
        /*@ model */ /*@ two_state */ boolean invariantMethod(int i, int __result);

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

        public static Counter $allocate();

        static private void $clprepare() {
        }
    }

    Counter makeCounter() {
        final int[] values = new int[1];
        return new Counter__1(values);
    }

    private static final class Counter__1 implements LambdaSideEffect.Counter {
        //@ represents footprint=_outer_final_values[0];
        //@ represents accessibleFields=_outer_final_values[0];

        public int apply(int i) {
            this._outer_final_values[0] = this._outer_final_values[0] + i;
            return this._outer_final_values[0];
        }

        private final int[] _outer_final_values;

        public Counter__1(int[] values) {
            this._outer_final_values = values;
        }

        //@ model booleanpreCondition(inti){return_outer_final_values[0] [@21,67:67='+',<249>,2:66] i [@25,71:72='>=',<235>,2:70] 0;}
        /*@ model */ boolean preCondition(int i);

        //@ model two_state booleanpostCondition(inti,int__result){return__result == _outer_final_values[0];}
        /*@ model */ /*@ two_state */ boolean postCondition(int i, int __result);

        //@ model two_state booleaninvariantMethod(inti,int__result){return__result [@25,80:81='>=',<235>,2:79] 0;}
        /*@ model */ /*@ two_state */ boolean invariantMethod(int i, int __result);

        /*@ model */ \locset footprint;

        /*@ model */ \locset accessibleFields;

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

        public static Counter__1 $allocate();

        public void $init(int[] values) {
            super.$init();
            this._outer_final_values = values;
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

    public static LambdaSideEffect $allocate();

    public LambdaSideEffect() {
    }

    public void $init() {
        super.$init();
        super.$init();
    }

    static private void $clprepare() {
    }
}
