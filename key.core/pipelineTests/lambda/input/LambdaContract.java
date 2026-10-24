class LambdaContract {
    interface IntFunction {
        /*@ model boolean preCondition(int i); */
        /*@ model two_state boolean postCondition(int i, int __result); */
        /*@ model two_state boolean invariantMethod(int i, int __result); */
        /*@ model \locset frameCondition(int i); */
        /*@ model \locset accessibleMethod(int i); */
        int apply(int i);
    }

    int cap = 100;

    IntFunction clamp() {
        int min = 5;
        final int step = 2;
        return (x) -> {
            //@ requires x >= min && x >= step;
            //@ ensures \result <= cap + step;
            //@ invariant \result >= 0;
            //@ assignable \nothing;
            //@ accessible cap;
            return x < (cap + step) ? (min + x) : x;
        };
    }
}
