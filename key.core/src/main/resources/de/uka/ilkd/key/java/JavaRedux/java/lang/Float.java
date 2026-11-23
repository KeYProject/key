package java.lang;

public class Float {
    public /*@ nullable @*/ final static java.lang.Class TYPE;

    private /*@ spec_public @*/ final float value;

    /*@ public normal_behavior
      @ ensures Float._isSame(\result.value, v);
      @ assignable \nothing;
      @*/
    public static java.lang.Float valueOf(float v);

    /*@ public normal_behavior
      @ ensures Float._isSame(value, v);
      @*/
    public Float(float v);

    /*@ public normal_behavior
      @ ensures Float._isSame(\result, value);
      @ assignable \strictly_nothing;
      @*/
    public float floatValue();

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
