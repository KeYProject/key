package java.lang;

public final class Boolean implements java.lang.Comparable, java.io.Serializable {
    public /*@ nullable @*/ final static java.lang.Class TYPE;

    private /*@ spec_public @*/ final boolean value;

    /*@ public normal_behavior
      @ ensures \result.value == v;
      @ assignable \nothing;
      @*/
    public static java.lang.Boolean valueOf(boolean v);

    /*@ public normal_behavior
      @ ensures value == v;
      @*/
    public Boolean(boolean v);

    /*@ public normal_behavior
      @ ensures \result == value;
      @ assignable \strictly_nothing;
      @*/
    public boolean booleanValue();
}
