class SwitchInSwitch {
    /*@ public normal_behavior
      @ ensures \result <==> a % 3 == 0;
      @ assignable \strictly_nothing;
      @*/
    public boolean m(int a) {
        outer: switch (a % 2) {
            case 0:
                switch (a % 3) {
                    case 2:
                        return false;
                    default:
                    case 0:
                        break;
                    case -1:
                        return false;
                }
            case 1:
                switch (a % 3) {
                    case 0:
                        return true;
                    case 1:
                        break;
                    default:
                        return false;
                    case 2:
                        break outer;
                }
            case -1:
                switch (a % 3) {
                    case 0:
                        return true;
                    case 2:
                        return false;
                }
        }
        return false;
    }
}
