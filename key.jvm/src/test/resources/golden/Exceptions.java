/* Golden M3 fixture: the exact source shape the KeY JVM transpiler emits for Exceptions --
 * javac-17's real try/catch bytecode reconstructed as structured Java try/catch blocks from
 * the exception table: the try range [start,end) becomes `try { }`, the handler (whose leading
 * astore binds the catch variable `local_<slot>`) is consumed into a real catch clause, the
 * finally-inlined catch-all handler rethrows the bound exception (`stk.push(local_2); throw`),
 * and athrow becomes a real `throw (Throwable)` (hence `throws Throwable`), with mid-layout
 * wrappers where javac's reachability demands them. The JML contracts of the original methods
 * are attached. All three proofs pin residuals of the §9.1(2) family (ExceptionsProofTest):
 * guarded's catch path pushes the literal 1, finallyFlow iconst_1/2 and an Object-typed
 * catch-all rethrow, thrower a String literal and an uncaught object creation. */
public class Exceptions {

    /*@ public normal_behavior
      @   ensures \result == (x < 0 ? x + 1 : x);
      @*/
    public static int guarded(int x) throws Throwable {
        jvm.Local stk = new jvm.Local();
        try {
            stk.push(x);
            if (stk.ifge()) { jvm.Local.goto_(8); }
            IllegalArgumentException $t0 = new IllegalArgumentException();
            stk.push($t0);
            if (true) { throw (Throwable) stk.popRef(); }
            L8: { if (false) { break L8; }
            stk.push(x);
            }
        } catch (IllegalArgumentException local_1) {
            stk.push(x);
            stk.push(1);
            stk.iadd();
            return stk.top();
        }
        return stk.top();
    }

    /*@ public normal_behavior
      @   requires x >= 0;
      @   ensures \result == x + 3;
      @*/
    public static int finallyFlow(int x) throws Throwable {
        int local_1;
        jvm.Local stk = new jvm.Local();
        stk.push(0);
        local_1 = stk.pop();
        try {
            stk.push(x);
            local_1 = stk.pop();
            stk.push(x);
            if (stk.ifge()) { jvm.Local.goto_(16); }
            IllegalArgumentException $t0 = new IllegalArgumentException();
            stk.push($t0);
            if (true) { throw (Throwable) stk.popRef(); }
            L16: { if (false) { break L16; }
            stk.push(local_1);
            stk.push(1);
            stk.iadd();
            local_1 = stk.pop();
            }
        } catch (Throwable local_2) {
            stk.push(local_1);
            stk.push(2);
            stk.iadd();
            local_1 = stk.pop();
            stk.push(local_2);
            if (true) { throw (Throwable) stk.popRef(); }
        }
        stk.push(local_1);
        stk.push(2);
        stk.iadd();
        local_1 = stk.pop();
        jvm.Local.goto_(44);
        L44: { if (false) { break L44; }
        stk.push(local_1);
        return stk.top();
        }
        return 0;
    }

    /*@ public normal_behavior
      @   requires x >= 0;
      @   ensures \result == x;
      @*/
    public static int thrower(int x) throws Throwable {
        jvm.Local stk = new jvm.Local();
        stk.push(x);
        if (stk.ifge()) { jvm.Local.goto_(9); }
        stk.push("boom");
        String $c0 = (String) stk.popRef();
        IllegalArgumentException $t1 = new IllegalArgumentException($c0);
        stk.push($t1);
        if (true) { throw (Throwable) stk.popRef(); }
        L9: { if (false) { break L9; }
        stk.push(x);
        return stk.top();
        }
        return 0;
    }

}
