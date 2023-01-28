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

    /*@ public model_behaviour
      @ requires true;
      @ accessible \nothing;
      @ static model boolean _isNaN(double val) {
      @     return val != val;
      @ }
      @*/

    /*@ public model_behaviour
      @ requires true;
      @ accessible \nothing;
      @ static model boolean _isSame(double a, double b) {
      @     return Double._isNaN(a) ? Double._isNaN(b) : a == b;
      @ }
      @*/
}
