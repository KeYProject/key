/**
 * Switch on an int that mixes breaking cases with fall-through AND places the
 * default branch in the middle. The default body has no break, so the default
 * case falls through into the following "case 1" body.
 *
 *   x == 0           -> 1     (case 0, break)
 *   x == 1           -> 5     (case 1, break)
 *   x == 2           -> 2     (case 2, break)
 *   otherwise        -> 104   (default sets 99, falls through into case 1: +5)
 */
public final class MixedFallthrough {

    /*@ public normal_behavior
      @   ensures x == 0 ==> \result == 1;
      @   ensures x == 1 ==> \result == 5;
      @   ensures x == 2 ==> \result == 2;
      @   ensures (x != 0 && x != 1 && x != 2) ==> \result == 104;
      @   assignable \strictly_nothing;
      @*/
    public int compute(int x) {
        int r = 0;
        switch (x) {
        case 0:
            r = 1;
            break;
        default:
            r = 99;
            // fall through into case 1
        case 1:
            r += 5;
            break;
        case 2:
            r = 2;
            break;
        }
        return r;
    }
}
