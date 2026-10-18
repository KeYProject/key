/* Golden M2 fixture: the exact source shape the KeY JVM transpiler emits for Caster --
 * checkcast pops the reference, performs the real Java cast (its ClassCastException obligation
 * is ruled out by `runtimeExceptions:ban` in proofs) and pushes the typed reference back;
 * instanceof pops the reference and pushes the JVM's int 0/1 result of the real instanceof.
 * Completed with the JML contracts of the original methods.
 *
 * The `classify` shape also exercises the constrained-goto pattern: the mid-layout return
 * that javac generates ahead of the second branch becomes `if (true) { return stk.top(); }`
 * followed by the guarded L9 label block.
 *
 * The proof side is subject to the Object-typed-op residual of the concept doc §9.1(2)
 * (push(Object) / popRef are Object-typed), so no closing gate exists yet; the emitted shape
 * is pinned by TranspileTest. */
public class Caster {

    /*@ public normal_behavior
      @   requires o instanceof Point;
      @   assignable \nothing;
      @   ensures \result == o;
      @*/
    public static Point asPoint(Object o) {
        jvm.Local stk = new jvm.Local();
        stk.push(o);
        Point $o0 = (Point) stk.popRef();
        stk.push($o0);
        return (Point) stk.topRef();
    }

    /*@ public normal_behavior
      @   assignable \nothing;
      @   ensures \result == (o instanceof Point ? 1 : 0);
      @*/
    public static int classify(Object o) {
        jvm.Local stk = new jvm.Local();
        stk.push(o);
        Object $o0 = (Object) stk.popRef();
        stk.push($o0 instanceof Point ? 1 : 0);
        if (stk.ifeq()) { jvm.Local.goto_(9); }
        stk.push(1);
        if (true) { return stk.top(); }
        L9: { if (false) { break L9; }
        stk.push(0);
        return stk.top();
        }
        return 0;
    }

}
