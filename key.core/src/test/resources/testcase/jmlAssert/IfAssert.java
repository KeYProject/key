public class IfAssert {
    /*@ normal_behavior
      @ requires true;
      @ ensures true;
      @*/
    public void m(int i) {
        if (i > 0) {
            //@ assert i > 0;
            i++;
        } else {
            i--;
        }
    }
}
