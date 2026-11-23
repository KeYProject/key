package java.lang;

public class Double {
    public /*@ nullable @*/ final static java.lang.Class TYPE;

    private /*@ spec_public @*/ final double value;

    /*@ public normal_behavior
      @ ensures Double._isSame(\result.value, v);
      @ assignable \nothing;
      @*/
    public static java.lang.Double valueOf(double v);

    /*@ public normal_behavior
      @ ensures Double._isSame(value, v);
      @*/
    public Double(double v);

    /*@ public normal_behavior
      @ ensures Double._isSame(\result, value);
      @ assignable \strictly_nothing;
      @*/
    public double doubleValue();

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
