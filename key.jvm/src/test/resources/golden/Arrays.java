/* Golden M2 fixture: the exact source shape the KeY JVM transpiler emits for Arrays --
 * newarray pops the length and pushes the real allocation (int[] slice only, other atypes
 * abort loudly), iaload/iastore/arraylength read and write the real int[] around typed
 * popRef casts of the array reference. Completed with the JML contracts of the original
 * methods.
 *
 * The proof side is subject to the Object-typed-op residual of the concept doc §9.1(2)
 * (push(a) / popRef of the array reference are Object-typed), so no closing gate exists yet;
 * the emitted shape is pinned by TranspileTest. */
public class Arrays {

    /*@ public normal_behavior
      @   requires a != null;
      @   assignable \nothing;
      @   ensures \result == a.length;
      @*/
    public static int length(int[] a) {
        jvm.Local stk = new jvm.Local();
        stk.push(a);
        int[] $a0 = (int[]) stk.popRef();
        stk.push($a0.length);
        return stk.top();
    }

    /*@ public normal_behavior
      @   requires a != null && 0 <= i && i < a.length;
      @   assignable \nothing;
      @   ensures \result == a[i];
      @*/
    public static int at(int[] a, int i) {
        jvm.Local stk = new jvm.Local();
        stk.push(a);
        stk.push(i);
        int $i0 = stk.pop();
        int[] $a1 = (int[]) stk.popRef();
        stk.push($a1[$i0]);
        return stk.top();
    }

    /*@ public normal_behavior
      @   requires a != null && 0 <= i && i < a.length;
      @   assignable a[i];
      @   ensures a[i] == v;
      @*/
    public static void set(int[] a, int i, int v) {
        jvm.Local stk = new jvm.Local();
        stk.push(a);
        stk.push(i);
        stk.push(v);
        int $v0 = stk.pop();
        int $i1 = stk.pop();
        int[] $a2 = (int[]) stk.popRef();
        $a2[$i1] = $v0;
        return;
    }

    /*@ public normal_behavior
      @   requires 0 <= n;
      @   assignable \nothing;
      @   ensures \result != null && \result.length == n;
      @*/
    public static int[] make(int n) {
        jvm.Local stk = new jvm.Local();
        stk.push(n);
        int[] $a0 = new int[stk.pop()];
        stk.push($a0);
        return (int[]) stk.topRef();
    }

}
