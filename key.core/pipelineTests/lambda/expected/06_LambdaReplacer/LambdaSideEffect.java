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

        //@ //@ model \locset footprint;
        //@ //@ model \locset accessibleFields;
        //@ //@ model boolean preCondition(int i);
        //@ //@ model two_state boolean postCondition(int i, int __result);
        //@ //@ model two_state boolean invariantMethod(int i, int __result);


        int apply(int i);
    }

    Counter makeCounter() {
        final int[] values = new int[1];
        final class Counter__1 implements LambdaSideEffect.Counter {

            public int apply(int i) {
                values[0] = values[0] + i;
                return values[0];
            }
        }
        return new Counter__1();
    }
}
