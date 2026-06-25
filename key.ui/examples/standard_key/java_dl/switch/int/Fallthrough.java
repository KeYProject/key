/**
 * Switch on an int that relies on FALL-THROUGH: none of the cases ends in a
 * break, so once a case is entered every following case body is executed as
 * well. The result is therefore a cumulative sum that depends on the entry
 * point.
 */
public final class Fallthrough {

    /*@ public normal_behavior
      @   requires 0 <= level && level <= 3;
      @   ensures level == 0 ==> \result == 10;
      @   ensures level == 1 ==> \result == 9;
      @   ensures level == 2 ==> \result == 7;
      @   ensures level == 3 ==> \result == 4;
      @   assignable \strictly_nothing;
      @*/
    public int accumulate(int level) {
        int r = 0;
        switch (level) {
        case 0:
            r += 1;
            // fall through
        case 1:
            r += 2;
            // fall through
        case 2:
            r += 3;
            // fall through
        case 3:
            r += 4;
        }
        return r;
    }
}
