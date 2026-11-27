package java.lang;

/**
 * Exists only for proving EVotingMachine
 */
public final class Character extends java.lang.Object implements java.io.Serializable, java.lang.Comparable
{
    public /*@ nullable @*/ final static java.lang.Class TYPE;

    private /*@ spec_public @*/ final char value;

    /*@ public normal_behavior
      @ ensures \result.value == v;
      @ assignable \nothing;
      @*/
    public static java.lang.Character valueOf(char v);

    /*@ public normal_behavior
      @ ensures value == v;
      @*/
    public Character(char v);

    /*@ public normal_behavior
      @ ensures \result == value;
      @ assignable \strictly_nothing;
      @*/
    public char charValue();

	static int digit(char ch, int radix);
}
