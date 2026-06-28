/**
 * Switch over a String with the default branch in the MIDDLE and no
 * fall-through (every branch returns). Uses correct .equals() String
 * semantics in the contract.
 */
public final class StringDefaultMiddle {

    /*@ public normal_behavior
      @   requires s != null;
      @   ensures s.equals("a") ==> \result == 1;
      @   ensures s.equals("b") ==> \result == 2;
      @   ensures s.equals("c") ==> \result == 3;
      @   ensures (!s.equals("a") && !s.equals("b") && !s.equals("c")) ==> \result == 0;
      @   assignable \strictly_nothing;
      @*/
    public int rank(String s) {
        String s1 = "b";
        s1 = "c";
        switch (s) {
        case "a":
            return 1;
        case "b":
            return 2;
        default:
            return 0;
        case "c":
            return 3;
        }
    }
}
