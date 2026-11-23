package java.lang;

public final class Short implements java.lang.Comparable {
    public final static short MIN_VALUE = (short) -32768;
    public final static short MAX_VALUE = (short) 32767;
    public /*@ nullable @*/ final static java.lang.Class TYPE;

    private /*@ spec_public @*/ final short value;

    /*@ public normal_behavior
      @ ensures \result.value == v;
      @ assignable \nothing;
      @*/
    public static java.lang.Short valueOf(short v);

    /*@ public normal_behavior
      @ ensures value == v;
      @*/
    public Short(short v);

    /*@ public normal_behavior
      @ ensures \result == value;
      @ assignable \strictly_nothing;
      @*/
    public short shortValue();
}
