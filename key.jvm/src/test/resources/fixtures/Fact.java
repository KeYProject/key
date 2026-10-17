/* JVM transpiler test fixture (M1): a recursive int method. The self-call exercises
 * operation-contract application at a recursion (\measured_by) against the jvm.Local
 * ghost-\seq stack model. */
public class Fact {

    /*@ public normal_behavior
      @ requires n >= 0;
      @ assignable \nothing;
      @ measured_by n;
      @ ensures \result >= 1;
      @ ensures n <= 1 ==> \result == 1;
      @*/
    public static int fact(int n) {
        if (n <= 1) {
            return 1;
        }
        return n * fact(n - 1);
    }
}
