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

        protected void $prepare() {
            super.$prepare();
            //Created by PrepareObjectBuilder.java:95
            this._outer_final_values = null;
        }

        private void $prepareEnter() {
            super.$prepare();
            //Created by PrepareObjectBuilder.java:95
            this._outer_final_values = null;
        }

        public Counter__1 $create() {
            //Created by CreateBuilder.java:58
            this.$initialized = false;
            $prepareEnter();
            return this;
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

    protected void $prepare() {
        super.$prepare();
    }

    private void $prepareEnter() {
        super.$prepare();
    }

    public LambdaSideEffect $create() {
        //Created by CreateBuilder.java:58
        this.$initialized = false;
        $prepareEnter();
        return this;
    }
}
