/* JVM transpiler test fixture (M3 stack shuffles): real javac-17 bytecode that exercises the
 * dup and dup2 stack rearrangements. dupReuse ((x = y) + x) compiles the result of the inner
 * assignment onto the stack via dup; dup2A (a[i] += v) duplicates array base + index for the
 * compound store via dup2. Shaped against golden/Shuffle.java; dupReuse (variable-only int)
 * closes under DefaultAutoMacro (ShuffleProofTest), dup2A stays in the §9.1(2) residual family. */
public class Shuffle {

    /*@ public normal_behavior
      @   ensures \result == 2 * y;
      @*/
    public static int dupReuse(int x, int y) {
        int r = (x = y) + x;
        return r;
    }

    /*@ public normal_behavior
      @   requires a != null && 0 <= i && i < a.length;
      @   assignable a[i];
      @   ensures a[i] == \old(a[i]) + v;
      @   ensures \result == \old(a[i]) + v;
      @*/
    public static int dup2A(int[] a, int i, int v) {
        a[i] += v;
        return a[i];
    }
}
