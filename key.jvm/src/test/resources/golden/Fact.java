/* Golden M1 fixture: the exact source shape the KeY JVM transpiler emits for Fact#fact
 * (static, recursive: a single jvm.Local frame, forward if_icmpgt goto, guarded label block,
 * the self-call re-emitted as pops into a temp followed by a real `stk.push(fact($v0))` call)
 * -- completed with the JML contract of the original method, whose `\measured_by` licenses the
 * recursive operation-contract application. The real transpiler output cannot carry the JML
 * (ASM strips it), so the proof tests run against this hand-written twin. */
public class Fact {

    /*@ public normal_behavior
      @ requires n >= 0;
      @ assignable \nothing;
      @ measured_by n;
      @ ensures \result >= 1;
      @ ensures n <= 1 ==> \result == 1;
      @*/
    public static int fact(int n) {
        jvm.Local stk = new jvm.Local();
        stk.push(n);
        stk.push(1);
        if (stk.if_icmpgt()) { jvm.Local.goto_(9); }
        stk.push(1);
        if (true) { return stk.top(); }
        L9: { if (false) { break L9; }
        stk.push(n);
        stk.push(n);
        stk.push(1);
        stk.isub();
        int $v0 = stk.pop();
        stk.push(fact($v0));
        stk.imul();
        return stk.top();
        }
        return 0;
    }
}
