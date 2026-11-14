/* JVM transpiler test fixture (M1): int-only methods covering forward gotos (max, max2),
 * a mid-layout return (max2) and backward loops (sum, fact). The pre/post specs are the
 * proof obligations the transpiled bodies are verified against. */
public class Max {

    /*@ public normal_behavior
      @ requires true;
      @ ensures \result == (a >= b ? a : b);
      @*/
    public int max(int a, int b) {
        return a >= b ? a : b;
    }

    /*@ public normal_behavior
      @ requires true;
      @ ensures \result == (a >= b ? a : b);
      @*/
    public int max2(int a, int b) {
        if (a >= b) {
            return a;
        } else {
            return b;
        }
    }

    /*@ public normal_behavior
      @ requires n >= 0;
      @ ensures \result == (\sum int i; 0 <= i && i < n; i);
      @*/
    public int sum(int n) {
        int s = 0;
        for (int i = 0; i < n; i++) {
            s += i;
        }
        return s;
    }

    /*@ public normal_behavior
      @ requires n >= 1;
      @ ensures \result == (\product int i; 1 <= i && i <= n; i);
      @*/
    public int fact(int n) {
        int r = 1;
        for (int i = 2; i <= n; i++) {
            r *= i;
        }
        return r;
    }
}
