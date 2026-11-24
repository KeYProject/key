/* Golden M3 fixture: the exact source shape the KeY JVM transpiler emits for Three — a bounded
 * javac-style `do {} while` loop. javac compiles the body + bottom-of-loop condition to
 * straight-line code whose restart is a *backward* `goto 4` (loop restart), which the transpiler
 * keeps as the backward `jvm.Local.goto_(8)` call inside the L8 block; the exit path
 * (`stk.push(local_0); return stk.top();`) sits inside the same block after the conditional jump.
 * Completed with the JML contract of the original method (`s == 3` after three iterations).
 * Auto mode drives this shape to termination purely through GotoRestoreRule unrolling (no
 * header split needed), so LoopProofTest asserts the proof closes — the backward-jump analog of
 * how the forward jumps in golden/Max.java close via GotoSpliceRule. */
public class Three {

    /*@ public normal_behavior
      @   ensures \result == 3;
      @*/
    public static int sum3() {
        int local_0;
        int local_1;
        jvm.Local stk = new jvm.Local();
        stk.push(0);
        local_0 = stk.pop();
        stk.push(0);
        local_1 = stk.pop();
        L8: { if (false) { break L8; }
        stk.push(local_0);
        stk.push(1);
        stk.iadd();
        local_0 = stk.pop();
        stk.push(local_1);
        stk.push(1);
        stk.iadd();
        local_1 = stk.pop();
        stk.push(local_1);
        stk.push(3);
        if (stk.if_icmplt()) { jvm.Local.goto_(8); }
        stk.push(local_0);
        return stk.top();
        }
        return 0;
    }

}
