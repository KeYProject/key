package java.lang;

public class Float {
    /*@ public normal_behaviour
      @ requires true;
      @ ensures \result == (val != val);
      @ assignable \strictly_nothing;
      @ accessible \nothing;
      @*/
    public static boolean isNaN(float val) {
        return val != val;
    }
}
