/* Golden M3 fixture: the exact source shape the KeY JVM transpiler emits for Restore -- the
 * infinite `do { s = s + 1; } while (true)` from fixtures/Restore.java. javac compiles the body
 * as straight-line code ending in a *backward* `goto 2` (loop restart), which the transpiler
 * keeps as the backward `jvm.Local.goto_(4)` call inside the L4 block. Auto mode applies
 * GotoRestoreRule to unroll the L4-suffix (no header split needed); the loop cannot terminate,
 * so the proof stays open -- KeY's repeated-state anti-looping bounds the unrolling and only
 * residual goals remain (LoopProofTest #infiniteLoopRestoreLeavesTheProofOpen). Completed with
 * the JML contract (the method never terminates normally, so nothing can be ensured beyond
 * `true`). */
public class Restore {

    /*@ public normal_behavior
      @   ensures true;
      @*/
    public static int spin() {
        int local_0;
        jvm.Local stk = new jvm.Local();
        stk.push(0);
        local_0 = stk.pop();
        L4: { if (false) { break L4; }
        stk.push(local_0);
        stk.push(1);
        stk.iadd();
        local_0 = stk.pop();
        jvm.Local.goto_(4);
        }
        return 0;
    }

}
