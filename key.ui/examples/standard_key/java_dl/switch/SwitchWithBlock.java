class SwitchWithBlock {
    /*@ public normal_behavior
      @ ensures \result <==> 0 <= a < 2;
      @ assignable \strictly_nothing;
      @*/
    public boolean m(int a) {
        int b = 0;
        switch (a) {
            case 0: l: {
                b++;
                break l;
            }
            b--;
            case 1: return true;
            default: return false;
        }
    }
}