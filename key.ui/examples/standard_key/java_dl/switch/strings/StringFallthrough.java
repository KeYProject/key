/**
 * Switch over a String that relies on FALL-THROUGH into a non-empty body:
 * the "a" case has no break and falls through into the "b" case, which then
 * breaks. Uses correct .equals() String semantics.
 *
 *   "a"        -> 3   (case "a": r += 1, falls through; case "b": r += 2)
 *   "b"        -> 2   (case "b": r += 2, break)
 *   otherwise  -> -1  (default)
 */
public final class StringFallthrough {

    /*@ public normal_behavior
      @   requires s != null;
      @   ensures s.equals("a") ==> \result == 3;
      @   ensures s.equals("b") ==> \result == 2;
      @   ensures (!s.equals("a") && !s.equals("b")) ==> \result == -1;
      @   assignable \strictly_nothing;
      @*/
    public int weight(String s) {
        int r = 0;
        switch (s) {
        case "a":
            r += 1;
            // fall through
        case "b":
            r += 2;
            break;
        default:
            r = -1;
        }
        return r;
    }
}
