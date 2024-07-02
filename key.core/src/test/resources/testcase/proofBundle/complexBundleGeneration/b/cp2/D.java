public class D {
    /*@ normal_behavior
      @ requires true;
      @ ensures \result == 5;
      @ assignable \strictly_nothing;
      @*/
    public int constant() {
        return 5;
    }
}
