package java.lang;

public final class Byte extends java.lang.Number implements java.lang.Comparable {
    public final static byte MIN_VALUE = (byte) -128;
    public final static byte MAX_VALUE = (byte) 127;
    public /*@ nullable @*/ final static java.lang.Class TYPE;

    private /*@ spec_public @*/ final byte value;

    /*@ public normal_behavior
      @ ensures \result.value == v;
      @ assignable \nothing;
      @*/
    public static java.lang.Byte valueOf(byte v);

    /*@ public normal_behavior
      @ ensures value == v;
      @*/
    public Byte(byte v);

    /*@ public normal_behavior
      @ ensures \result == value;
      @ assignable \strictly_nothing;
      @*/
    public byte byteValue();

    /*@ public normal_behavior
      @ ensures \result == (int) value;
      @ assignable \strictly_nothing;
      @*/
    public int intValue();
    /*@ public normal_behavior
      @ ensures \result == (long) value;
      @ assignable \strictly_nothing;
      @*/
    public long longValue();

    // The result is unconstrained: KeY has no cast axiomatisation to relate it to value.
    /*@ public normal_behavior
      @ assignable \strictly_nothing;
      @*/
    public short shortValue();
}
