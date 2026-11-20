/* Golden M2 fixture: the exact source shape the KeY JVM transpiler emits for Shapes (total
 * reading Point's fields through jvm.Local, make fusing new+dup+invokespecial into a real
 * allocation "Point $t2 = new Point($c1, $c0);" and calling sum on the receiver) -- completed
 * with the JML contracts of the original methods. */
public class Shapes {

    /*@ public normal_behavior
      @   requires p != null;
      @   assignable \nothing;
      @   ensures \result == p.x + p.y;
      @*/
    public static int total(Point p) {
        jvm.Local stk = new jvm.Local();
        stk.push(p);
        Point $o0 = (Point) stk.popRef();
        stk.push($o0.x);
        stk.push(p);
        Point $o1 = (Point) stk.popRef();
        stk.push($o1.y);
        stk.iadd();
        return stk.top();
    }

    /*@ public normal_behavior
      @   assignable \nothing;
      @   ensures \result == 3;
      @*/
    public static int make() {
        Point local_0;
        jvm.Local stk = new jvm.Local();
        stk.push(1);
        stk.push(2);
        int $c0 = stk.pop();
        int $c1 = stk.pop();
        Point $t2 = new Point($c1, $c0);
        stk.push($t2);
        local_0 = (Point) stk.popRef();
        stk.push(local_0);
        Point $o3 = (Point) stk.popRef();
        stk.push($o3.sum());
        return stk.top();
    }

}
