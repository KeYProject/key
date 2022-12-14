package java.lang;

public class Double {
    /*@ public normal_behaviour
      @ requires true;
      @ ensures \result == (val != val);
      @ assignable \strictly_nothing;
      @ accessible \nothing;
      @*/
    public static boolean isNaN(double val) {
        return val != val;
    }
}
