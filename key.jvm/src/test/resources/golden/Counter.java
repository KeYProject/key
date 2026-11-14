/* Golden M2 fixture: the exact source shape the KeY JVM transpiler emits for Counter --
 * getstatic/putstatic read and write the real static field through jvm.Local (int via pop(),
 * references via the typed popRef cast), a boolean value would be int-normalized, and
 * <clinit> initializers are dropped, so static fields start at their JVM defaults (0 / null),
 * matching the `initialisation:disableStaticInitialisation` proof setting. Completed with the
 * JML contracts of the original methods.
 *
 * The proof side of this class is subject to the Object-typed-op residual of the concept doc
 * §9.1(2) (stk.push(Counter.mark) / popRef / topRef are Object-typed), so no closing gate
 * exists yet; the emitted shape is pinned by TranspileTest. */
public class Counter {

    public static int calls;

    public static Point mark;

    /*@ public normal_behavior
      @   assignable calls;
      @   ensures calls == \old(calls) + 1 && \result == calls;
      @*/
    public static int next() {
        jvm.Local stk = new jvm.Local();
        stk.push(Counter.calls);
        stk.push(1);
        stk.iadd();
        int $v0 = stk.pop();
        Counter.calls = $v0;
        stk.push(Counter.calls);
        return stk.top();
    }

    /*@ public normal_behavior
      @   assignable \nothing;
      @   ensures \result == mark;
      @*/
    public static Point current() {
        jvm.Local stk = new jvm.Local();
        stk.push(Counter.mark);
        return (Point) stk.topRef();
    }

    /*@ public normal_behavior
      @   assignable mark;
      @   ensures mark == p;
      @*/
    public static void remember(Point p) {
        jvm.Local stk = new jvm.Local();
        stk.push(p);
        Point $v0 = (Point) stk.popRef();
        Counter.mark = $v0;
        return;
    }

}
