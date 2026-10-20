/* Golden M3 fixture: the exact source shape the KeY JVM transpiler emits for Shuffle --
 * the stack-rearrangement calls of the runtime model javac-17's real dup/dup2 bytecode:
 * (x = y) + x emits `stk.push(y); stk.dup(); x = stk.pop(); ...` and the int-array compound
 * a[i] += v emits `stk.push(a); stk.push(i); stk.dup2(); ...`. Completed with the JML
 * contracts of the original methods. dupReuse is variable-only int and closes under
 * DefaultAutoMacro (ShuffleProofTest); dup2A carries the array/ref residual of §9.1(2). */
public class Shuffle {

    /*@ public normal_behavior
      @   ensures \result == 2 * y;
      @*/
    public static int dupReuse(int x, int y) {
        int local_2;
        jvm.Local stk = new jvm.Local();
        stk.push(y);
        stk.dup();
        x = stk.pop();
        stk.push(x);
        stk.iadd();
        local_2 = stk.pop();
        stk.push(local_2);
        return stk.top();
    }

    /*@ public normal_behavior
      @   requires a != null && 0 <= i && i < a.length;
      @   assignable a[i];
      @   ensures a[i] == \old(a[i]) + v;
      @   ensures \result == \old(a[i]) + v;
      @*/
    public static int dup2A(int[] a, int i, int v) {
        jvm.Local stk = new jvm.Local();
        stk.push(a);
        stk.push(i);
        stk.dup2();
        int $i0 = stk.pop();
        int[] $a1 = (int[]) stk.popRef();
        stk.push($a1[$i0]);
        stk.push(v);
        stk.iadd();
        int $v2 = stk.pop();
        int $i3 = stk.pop();
        int[] $a4 = (int[]) stk.popRef();
        $a4[$i3] = $v2;
        stk.push(a);
        stk.push(i);
        int $i5 = stk.pop();
        int[] $a6 = (int[]) stk.popRef();
        stk.push($a6[$i5]);
        return stk.top();
    }

}
