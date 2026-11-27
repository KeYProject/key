/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2,
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */

/**
 * Example for the specification and verification of lambda expressions in KeY.
 *
 * <p>KeY desugars lambda expressions into anonymous local classes implementing
 * the functional interface (following Alexander Csiky's transformation-based
 * approach). The JML contract of the lambda body is converted into
 * <em>model methods</em> on the generated class:
 *
 * <ul>
 *   <li>{@code requires}   &rarr; {@code preCondition(...)}</li>
 *   <li>{@code ensures}    &rarr; {@code postCondition(...)}</li>
 *   <li>{@code assignable} &rarr; {@code frameCondition(...)}</li>
 * </ul>
 *
 * <p>The functional interface declares the model methods that give the
 * converted contract its shape, and its abstract method {@code apply} is
 * specified against them. The generated implementation of {@code apply} (here:
 * the desugared lambda returned by {@link #triple()}) is automatically proven
 * against this contract, i.e. a {@code preCondition} that is met, a
 * {@code postCondition} that follows from the lambda body, and a frame that is
 * respected. See the proof obligation in {@code project.key}.
 */
public class Lambdas {

    /**
     * Functional interface whose model methods give the lambda contract its
     * shape. {@code postCondition} is {@code two_state}: the second parameter
     * {@code __result} will hold the return value of the functional method.
     */
    interface IntFunction {
        /*@ model boolean preCondition(int i); */
        /*@ model two_state boolean postCondition(int i, int __result); */
        /*@ model \locset frameCondition(int i); */

        /*@ normal_behavior
          @ requires preCondition(x);
          @ ensures postCondition(x, \result);
          @ assignable frameCondition(x);
          @*/
        int apply(int x);
    }

    /**
     * A lambda expression together with its specification. The clauses in the
     * body of the lambda are converted into definitions of the model methods
     * of the desugared class:
     *
     * <pre>
     * //@ model boolean preCondition(int i)              { return i &gt;= 0; }
     * //@ model two_state boolean postCondition(int i, int __result) { return __result == 3 * i; }
     * //@ model \locset frameCondition(int i)            { return \locset(\nothing); }
     * </pre>
     *
     * The proof obligation checks that the implementation of {@code apply}
     * (the lambda body) satisfies the contract derived this way.
     */
    static IntFunction triple() {
        IntFunction t = x -> {
            //@ requires x >= 0;
            //@ ensures \result == 3 * x;
            //@ assignable \nothing;
            return 3 * x;
        };
        return t;
    }
}
