public class Result {
    /*@ public normal_behaviour
      @ ensures \result == result;
      @*/
    public int test(int result) {
        return result;
    }
}
