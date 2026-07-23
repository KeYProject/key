public class Para {
    /*@ public normal_behaviour
      @ requires para_0 >= 0;
      @ ensures \result == para_0;
      @*/
    public int test(int para_0) {
        return para_0;
    }
}
