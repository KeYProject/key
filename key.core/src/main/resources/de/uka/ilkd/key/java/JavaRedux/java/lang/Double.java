package java.lang;

public class Double extends java.lang.Number {
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

    /*@ public normal_behavior
      @ ensures \result == (int) value;
      @ assignable \strictly_nothing;
      @*/
    public int intValue();

    /*@ public normal_behavior
      @ assignable \strictly_nothing;
      @*/
    public short shortValue();

    // The result is unconstrained: KeY has no cast axiomatisation to relate it to value.
    /*@ public normal_behavior
      @ assignable \strictly_nothing;
      @*/
    public byte byteValue();

    /*@ public normal_behavior
      @ ensures \result == (long) value;
      @ assignable \strictly_nothing;
      @*/
    public long longValue();
}
