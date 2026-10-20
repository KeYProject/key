/* JVM transpiler test fixture (M3 exceptions): real javac-17 try/catch bytecode — an
 * explicitly thrown, caught IllegalArgumentException with a negative guard (guarded), a
 * finally block as javac inlines it (catch-any handler in the exception table that rethrows
 * after the finally body; finallyFlow), and an uncaught throw carrying a String message
 * (thrower). Proof fixtures must not use idiv or array indexing (both are contractless or
 * blocked by the runtimeExceptions: ban settings), so the errors are raised by explicit
 * throw. guarded is deliberately constant-free on the normal path so the exception-boundary
 * mechanics (try/catch structure, catch binding, athrow) can be observed in isolation; the
 * catch path's x + 1 and finallyFlow's iconst_1/2 pin them in the §9.1(2) residual family
 * (ExceptionsProofTest). */
public class Exceptions {

    /*@ public normal_behavior
      @   ensures \result == (x < 0 ? x + 1 : x);
      @*/
    public static int guarded(int x) {
        try {
            if (x < 0) throw new IllegalArgumentException();
            return x;
        } catch (IllegalArgumentException e) {
            return x + 1;
        }
    }

    /*@ public normal_behavior
      @   requires x >= 0;
      @   ensures \result == x + 3;
      @*/
    public static int finallyFlow(int x) {
        int r = 0;
        try {
            r = x;
            if (x < 0) throw new IllegalArgumentException();
            r = r + 1;
        } finally {
            r = r + 2;
        }
        return r;
    }

    /*@ public normal_behavior
      @   requires x >= 0;
      @   ensures \result == x;
      @*/
    public static int thrower(int x) {
        if (x < 0) throw new IllegalArgumentException("boom");
        return x;
    }
}
