/**
 * Switch over a String WITHOUT a default branch. The precondition restricts
 * the selector to the labelled values (by value), so the trailing return is
 * never reached. Uses correct .equals() String semantics.
 */
public final class StringNoDefault {

    /*@ public normal_behavior
      @   requires s != null;
      @   requires s.equals("yes") || s.equals("no");
      @   ensures s.equals("yes") ==> \result == 1;
      @   ensures s.equals("no")  ==> \result == 0;
      @   assignable \strictly_nothing;
      @*/
    public int toBool(String s) {
        switch (s) {
        case "yes":
            return 1;
        case "no":
            return 0;
        }
        return -1; // unreachable under the precondition
    }
}
