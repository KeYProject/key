/* JVM transpiler test fixture (M3 category-2): real javac-17 bytecode for long, double and
 * float arithmetic, conversions, lcmp-branches and long-array compounds. ladd, conv, back,
 * flt are variable-only flows (no constant reaches the \seq) and close under
 * DefaultAutoMacro (Category2ProofTest); lconst, dbl and mix carry literals and stay in the
 * §9.1(2) residual family; larray is Object-typed (long[]) traffic. The shape is asserted
 * against golden/Category2.java. */
public class Category2 {

    /*@ public normal_behavior
      @   ensures \result == a + b;
      @*/
    public static long ladd(long a, long b) {
        return a + b;
    }

    /*@ public normal_behavior
      @   ensures \result == 42L;
      @*/
    public static long lconst() {
        return 42L;
    }

    /*@ public normal_behavior
      @   ensures \result == (a < b ? a : b);
      @*/
    public static long lcmpish(long a, long b) {
        return a < b ? a : b;
    }

    /*@ public normal_behavior
      @   ensures \result == (long) x;
      @*/
    public static long conv(int x) {
        return x;
    }

    /*@ public normal_behavior
      @   ensures \result == (int) x;
      @*/
    public static int back(long x) {
        return (int) x;
    }

    /*@ public normal_behavior
      @   ensures \result == a * 2.0;
      @*/
    public static double dbl(double a) {
        return a * 2.0;
    }

    /*@ public normal_behavior
      @   ensures \result == (double) i + 0.5;
      @*/
    public static double mix(int i) {
        return i + 0.5;
    }

    /*@ public normal_behavior
      @   ensures \result == a * b;
      @*/
    public static float flt(float a, float b) {
        return a * b;
    }

    /*@ public normal_behavior
      @   ensures \result == (c ? d1 : d2);
      @*/
    public static double ternary(boolean c, double d1, double d2) {
        return c ? d1 : d2;
    }

    /*@ public normal_behavior
      @   requires a != null && 0 <= i && i < a.length;
      @   assignable a[i];
      @   ensures a[i] == \old(a[i]) + v;
      @   ensures \result == \old(a[i]) + v;
      @*/
    public static long larray(long[] a, int i, long v) {
        a[i] += v;
        return a[i];
    }
}
