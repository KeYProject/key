public class LargeSwitch {
    /*@ public normal_behavior
      @ requires 0 <= n;
      @ ensures \result == n % 3;
      @ assignable \strictly_nothing;
      @*/
    public int m(int n) {
        switch (n) {
        case 0:
        case 15:
        case 18:
        case 21:
            return 0;
        case 1:
        case 16:
        case 19:
        case 22:
            return 1;
        case 2:
        case 17:
        case 20:
        case 23:
            return 2;
        case 3:
        case 24:
        case 27:
        case 30:
            return 0;
        case 4:
        case 25:
        case 28:
        case 31:
            return 1;
        case 5:
        case 26:
        case 29:
        case 32:
            return 2;
        case 6:
            return 0;
        case 7:
            return 1;
        case 8:
            return 2;
        case 9:
            return 0;
        case 10:
            return 1;
        case 11:
            return 2;
        case 12:
            return 0;
        case 13:
            return 1;
        case 14:
            return 2;
        default:
            return n % 3;
        }
    }
}
