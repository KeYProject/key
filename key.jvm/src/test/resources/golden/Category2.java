/* Golden M3 fixture: the exact source shape the KeY JVM transpiler emits for Category2 --
 * the long/double/float slice of the runtime model: category-2 locals via pushL/pushD/pushF
 * and popL/popD/popF, ladd/lcmp/i2l/l2i/dmul/dadd/fmul/d2i-style mnemonics, ldc2_w constants
 * as pushL(42L)/pushD(2.0), lcmp feeding the following ifge (branch on its pushed sign),
 * goto-merge of the `c ? d1 : d2` ternary, and the dup2 + laload/lastore pair of the long-array
 * compound -- completed with the JML contracts of the original methods. ladd, conv, back and
 * flt are variable-only and close under DefaultAutoMacro (Category2ProofTest); the literal-
 * carrying lconst/dbl/mix and the Object-typed larray stay in the §9.1(2) residual family. */
public class Category2 {

    /*@ public normal_behavior
      @   ensures \result == a + b;
      @*/
    public static long ladd(long a, long b) {
        jvm.Local stk = new jvm.Local();
        stk.pushL(a);
        stk.pushL(b);
        stk.ladd();
        return stk.topL();
    }

    /*@ public normal_behavior
      @   ensures \result == 42L;
      @*/
    public static long lconst() {
        jvm.Local stk = new jvm.Local();
        stk.pushL(42L);
        return stk.topL();
    }

    /*@ public normal_behavior
      @   ensures \result == (a < b ? a : b);
      @*/
    public static long lcmpish(long a, long b) {
        jvm.Local stk = new jvm.Local();
        stk.pushL(a);
        stk.pushL(b);
        stk.lcmp();
        if (stk.ifge()) { jvm.Local.goto_(8); }
        stk.pushL(a);
        jvm.Local.goto_(11);
        L8: { if (false) { break L8; }
        stk.pushL(b);
        }
        L11: { if (false) { break L11; }
        return stk.topL();
        }
        return 0L;
    }

    /*@ public normal_behavior
      @   ensures \result == (long) x;
      @*/
    public static long conv(int x) {
        jvm.Local stk = new jvm.Local();
        stk.push(x);
        stk.i2l();
        return stk.topL();
    }

    /*@ public normal_behavior
      @   ensures \result == (int) x;
      @*/
    public static int back(long x) {
        jvm.Local stk = new jvm.Local();
        stk.pushL(x);
        stk.l2i();
        return stk.top();
    }

    /*@ public normal_behavior
      @   ensures \result == a * 2.0;
      @*/
    public static double dbl(double a) {
        jvm.Local stk = new jvm.Local();
        stk.pushD(a);
        stk.pushD(2.0);
        stk.dmul();
        return stk.topD();
    }

    /*@ public normal_behavior
      @   ensures \result == (double) i + 0.5;
      @*/
    public static double mix(int i) {
        jvm.Local stk = new jvm.Local();
        stk.push(i);
        stk.i2d();
        stk.pushD(0.5);
        stk.dadd();
        return stk.topD();
    }

    /*@ public normal_behavior
      @   ensures \result == a * b;
      @*/
    public static float flt(float a, float b) {
        jvm.Local stk = new jvm.Local();
        stk.pushF(a);
        stk.pushF(b);
        stk.fmul();
        return stk.topF();
    }

    /*@ public normal_behavior
      @   ensures \result == (c ? d1 : d2);
      @*/
    public static double ternary(boolean c, double d1, double d2) {
        jvm.Local stk = new jvm.Local();
        stk.push((c ? 1 : 0));
        if (stk.ifeq()) { jvm.Local.goto_(6); }
        stk.pushD(d1);
        jvm.Local.goto_(9);
        L6: { if (false) { break L6; }
        stk.pushD(d2);
        }
        L9: { if (false) { break L9; }
        return stk.topD();
        }
        return 0.0;
    }

    /*@ public normal_behavior
      @   requires a != null && 0 <= i && i < a.length;
      @   assignable a[i];
      @   ensures a[i] == \old(a[i]) + v;
      @   ensures \result == \old(a[i]) + v;
      @*/
    public static long larray(long[] a, int i, long v) {
        jvm.Local stk = new jvm.Local();
        stk.push(a);
        stk.push(i);
        stk.dup2();
        int $i0 = stk.pop();
        long[] $a1 = (long[]) stk.popRef();
        stk.pushL($a1[$i0]);
        stk.pushL(v);
        stk.ladd();
        long $v2 = stk.popL();
        int $i3 = stk.pop();
        long[] $a4 = (long[]) stk.popRef();
        $a4[$i3] = $v2;
        stk.push(a);
        stk.push(i);
        int $i5 = stk.pop();
        long[] $a6 = (long[]) stk.popRef();
        stk.pushL($a6[$i5]);
        return stk.topL();
    }

}
