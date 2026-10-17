/* Golden M1 fixture: the exact source shape the KeY JVM transpiler emits for Max#max and
 * Max#max2 (a single jvm.Local frame whose \seq ghost models the operand stack, plain-Java
 * locals for parameters, forward goto on the if_icmplt result, guarded label blocks,
 * jvm.Local.goto_ calls, wrapped mid-layout return in max2) -- completed with the JML
 * contracts of the original methods. The real transpiler output cannot carry the JML (ASM
 * strips it), so the proof tests run against this hand-written twin; the transpiler's fidelity
 * to this shape is checked by TranspileTest. */
public class Max {

    /*@ public normal_behavior
      @ requires true;
      @ ensures \result == (a >= b ? a : b);
      @*/
    public int max(int a, int b) {
        jvm.Local stk = new jvm.Local();
        stk.push(a);
        stk.push(b);
        if (stk.if_icmplt()) { jvm.Local.goto_(7); }
        stk.push(a);
        jvm.Local.goto_(10);
        L7: { if (false) { break L7; }
        stk.push(b);
        }
        L10: { if (false) { break L10; }
        return stk.top();
        }
        return 0;
    }

    /*@ public normal_behavior
      @ requires true;
      @ ensures \result == (a >= b ? a : b);
      @*/
    public int max2(int a, int b) {
        jvm.Local stk = new jvm.Local();
        stk.push(a);
        stk.push(b);
        if (stk.if_icmplt()) { jvm.Local.goto_(9); }
        stk.push(a);
        if (true) { return stk.top(); }
        L9: { if (false) { break L9; }
        stk.push(b);
        return stk.top();
        }
        return 0;
    }
}
