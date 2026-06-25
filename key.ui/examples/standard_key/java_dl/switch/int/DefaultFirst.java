/**
 * Switch on an int with the default branch in the FIRST position and no
 * fall-through: every branch (default included) ends in a return, so the
 * textual position of the default does not influence the behaviour.
 */
public final class DefaultFirst {

    /*@ public normal_behavior
      @   ensures x == 1 ==> \result == 10;
      @   ensures x == 2 ==> \result == 20;
      @   ensures (x != 1 && x != 2) ==> \result == 0;
      @   assignable \strictly_nothing;
      @*/
    public int classify(int x) {
        switch (x) {
        default:
            return 0;
        case 1:
            return 10;
        case 2:
            return 20;
        }
    }
}
