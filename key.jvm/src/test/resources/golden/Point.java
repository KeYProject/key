/* Golden M2 fixture: the exact source shape the KeY JVM transpiler emits for Point (fields,
 * explicit constructor whose super.<init>() is dropped and whose field writes go through
 * jvm.Local, instance method sum reading the real fields) -- completed with the JML contracts of
 * the original methods. The real transpiler output cannot carry the JML (ASM strips it), so the
 * proof tests run against this hand-written twin; the transpiler's fidelity to this shape is
 * checked by TranspileTest. */
public class Point {

    public int x;

    public int y;

    /*@ public normal_behavior
      @   requires true;
      @   assignable x, y;
      @   ensures x == a && y == b;
      @*/
    public Point(int a, int b) {
        jvm.Local stk = new jvm.Local();
        stk.push(this);
        stk.popRef();
        stk.push(this);
        stk.push(a);
        int $v0 = stk.pop();
        Point $o1 = (Point) stk.popRef();
        $o1.x = $v0;
        stk.push(this);
        stk.push(b);
        int $v2 = stk.pop();
        Point $o3 = (Point) stk.popRef();
        $o3.y = $v2;
        return;
    }

    /*@ public normal_behavior
      @   assignable \nothing;
      @   ensures \result == x + y;
      @*/
    public int sum() {
        jvm.Local stk = new jvm.Local();
        stk.push(this);
        Point $o0 = (Point) stk.popRef();
        stk.push($o0.x);
        stk.push(this);
        Point $o1 = (Point) stk.popRef();
        stk.push($o1.y);
        stk.iadd();
        return stk.top();
    }

}
