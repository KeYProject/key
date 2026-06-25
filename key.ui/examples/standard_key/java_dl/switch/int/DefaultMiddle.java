/**
 * Switch on an int with the default branch in the MIDDLE and no fall-through:
 * every branch ends in a return, so even though "default" sits between the
 * cases it only ever applies to values not matched by any case label.
 */
public final class DefaultMiddle {

    /*@ public normal_behavior
      @   ensures x == 1 ==> \result == 10;
      @   ensures x == 2 ==> \result == 20;
      @   ensures x == 3 ==> \result == 30;
      @   ensures (x != 1 && x != 2 && x != 3) ==> \result == -1;
      @   assignable \strictly_nothing;
      @*/
    public int classify(int x) {
        switch (x) {
        case 1:
            return 10;
        case 2:
            return 20;
        default:
            return -1;
        case 3:
            return 30;
        }
    }
}
