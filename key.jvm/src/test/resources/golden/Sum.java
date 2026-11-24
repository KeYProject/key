/* Golden M3 fixture: the exact source shape the KeY JVM transpiler emits for Sum --
 * a javac-style `while` loop. javac compiles the loop header+body to a *backward* goto
 * (pc 17: `goto 4`), which the transpiler keeps as the backward `jvm.Local.goto_(8)` call
 * inside the L8 block — loops are NOT structured by the transpiler (§3.4's structured
 * `while` emission is a planned optimization, not shipped behavior). The exit of this shape is a
 * symbolic `if (stk.if_icmpge())` split; auto mode drives the iterations via GotoRestoreRule
 * unrolling and leaves the §9.1(2) createdness residuals open (LoopProofTest
 * #autoModeDrivesThroughLoopsWithoutLeavingAnActiveJump). Completed with the JML contract of the
 * original method (sum of 0..n-1). */
public class Sum {

    /*@ public normal_behavior
      @   requires n >= 0;
      @   ensures \result == n * (n - 1) / 2;
      @*/
    public static int whileSum(int n) {
        int local_1;
        int local_2;
        jvm.Local stk = new jvm.Local();
        stk.push(0);
        local_1 = stk.pop();
        stk.push(0);
        local_2 = stk.pop();
        L8: { if (false) { break L8; }
        stk.push(local_2);
        stk.push(n);
        if (stk.if_icmpge()) { jvm.Local.goto_(27); }
        stk.push(local_1);
        stk.push(local_2);
        stk.iadd();
        local_1 = stk.pop();
        stk.push(local_2);
        stk.push(1);
        stk.iadd();
        local_2 = stk.pop();
        jvm.Local.goto_(8);
        }
        L27: { if (false) { break L27; }
        stk.push(local_1);
        return stk.top();
        }
        return 0;
    }

}
