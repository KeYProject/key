/**
 * Switch on an int that groups several case labels for a shared body (empty
 * fall-through between the labels) and closes with a default branch. Maps a
 * month number 1..12 to a season code and yields -1 for any other value.
 */
public final class FallthroughGroups {

    /*@ public normal_behavior
      @   ensures (month == 12 || month == 1 || month == 2) ==> \result == 0;
      @   ensures (3 <= month && month <= 5)  ==> \result == 1;
      @   ensures (6 <= month && month <= 8)  ==> \result == 2;
      @   ensures (9 <= month && month <= 11) ==> \result == 3;
      @   ensures (month < 1 || month > 12)   ==> \result == -1;
      @   assignable \strictly_nothing;
      @*/
    public int season(int month) {
        switch (month) {
        case 12:
        case 1:
        case 2:
            return 0;
        case 3:
        case 4:
        case 5:
            return 1;
        case 6:
        case 7:
        case 8:
            return 2;
        case 9:
        case 10:
        case 11:
            return 3;
        default:
            return -1;
        }
    }
}
