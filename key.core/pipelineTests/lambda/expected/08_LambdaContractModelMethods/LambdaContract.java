class LambdaContract {

    interface IntFunction {

        //@ /*@ model boolean preCondition(int i); */
        //@ /*@ model two_state boolean postCondition(int i, int __result); */
        //@ /*@ model two_state boolean invariantMethod(int i, int __result); */
        //@ /*@ model \locset frameCondition(int i); */
        //@ /*@ model \locset accessibleMethod(int i); */


        int apply(int i);
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

        //@ model boolean preCondition(int x) { return x >= _outer_final_min && x >= _outer_final_step; }


        //@ model two_state boolean postCondition(int x, int __result) { return __result <= outer_this.cap + _outer_final_step; }


        //@ model two_state boolean invariantMethod(int x, int __result) { return __result >= 0; }


        //@ model \locset frameCondition(int x) { return \locset(\nothing); }


        //@ model \locset accessibleMethod(int x) { return \locset(outer_this.cap); }

    }
}
