/**
 * Switch over a REFERENCE type (String) with the default branch last and no
 * fall-through.
 *
 * The contract uses the CORRECT String semantics: a case matches when the
 * selector is .equals() to the label, not when it is reference-identical.
 * This is intended as a test for a switch treatment that handles Strings by
 * value. A null selector throws a NullPointerException in Java, hence
 * "requires s != null".
 */
public final class StringDefaultLast {

    /*@ public normal_behavior
      @   requires s != null;
      @   ensures s.equals("red")   ==> \result == 0;
      @   ensures s.equals("green") ==> \result == 1;
      @   ensures s.equals("blue")  ==> \result == 2;
      @   ensures (!s.equals("red") && !s.equals("green") && !s.equals("blue"))
      @           ==> \result == -1;
      @   assignable \strictly_nothing;
      @*/
    public int code(String s) {
        String s1 = "green";
        s1 = "blue";
        switch (s) {
        case "red":
            return 0;
        case "green":
            return 1;
        case "blue":
            return 2;
        default:
            return -1;
        }
    }
}
