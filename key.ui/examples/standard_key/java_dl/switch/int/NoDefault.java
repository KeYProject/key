/**
 * Switch on an int WITHOUT a default branch and no fall-through. The
 * precondition restricts the argument to the labelled values, so the trailing
 * return statement (required by Java because the switch is not exhaustive) is
 * never reached.
 */
public final class NoDefault {

    /*@ public normal_behavior
      @   requires 1 <= day && day <= 3;
      @   ensures day == 1 ==> \result == 100;
      @   ensures day == 2 ==> \result == 200;
      @   ensures day == 3 ==> \result == 300;
      @   assignable \strictly_nothing;
      @*/
    public int points(int day) {
        switch (day) {
        case 1:
            return 100;
        case 2:
            return 200;
        case 3:
            return 300;
        }
        return -1; // unreachable under the precondition
    }
}
