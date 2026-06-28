/**
 * Switch on an int with the default branch in the LAST position and no
 * fall-through: every case ends in a return.
 *
 * The contract specifies the expected result for every input value.
 */
public final class DefaultLast {

    /*@ public normal_behavior
      @   ensures x == 0 ==> \result == 10;
      @   ensures x == 1 ==> \result == 20;
      @   ensures x == 2 ==> \result == 30;
      @   ensures (x < 0 || x > 2) ==> \result == -1;
      @   assignable \strictly_nothing;
      @*/
    public int classify(int x) {
        switch (x) {
        case 0:
            return 10;
        case 1:
            return 20;
        case 2:
            return 30;
        default:
            return -1;
        }
    }
}
