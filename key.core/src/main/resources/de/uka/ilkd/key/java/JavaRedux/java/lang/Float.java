package java.lang;

public class Float {
    /*@ public normal_behaviour
      @ requires true;
      @ ensures \result == Float._isNaN(val);
      @ assignable \strictly_nothing;
      @*/
    public static boolean isNaN(float val) {
        return val != val;
    }

    /*@ public model_behaviour
      @ requires true;
      @ accessible \nothing;
      @ static model boolean _isNaN(float val) {
      @     return val != val;
      @ }
      @*/

    /*@ public model_behaviour
      @ requires true;
      @ accessible \nothing;
      @ static model boolean _isSame(float a, float b) {
      @     return Float._isNaN(a) ? Float._isNaN(b) : a == b;
      @ }
      @*/
}
