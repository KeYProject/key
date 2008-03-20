
package java.lang;

/** not all features that are documented in sun's api for java.lang.Enum are 
 * supported by this model.
 * 
 * In the original class some methods are implemented final and implement the
 * same behaviour as the corresponding method in java.lang.Object. These methods
 * can be omitted here as we suppose the programs have no compile-time errors. 
 */

public abstract class Enum implements Comparable, java.io.Serializable {
 
    /** The ordinal is what is returned by the ordinal()-function
     * and will be resolved by a taclet as the definition is beyond jml
     */
    private int ordinal;

    /** the getter for the name of this enum constant */
    /* @ pure 
      @ public normal_behavior
      @    valueOf(\result) == this
      @*/
    public final String name();

    /** the getter for the number in the definition order of this constant */
    /*@ public normal_behavior
      @   requires   true
      @   ensures    \result = ordinal
      @   pure
      @*/
    public final int ordinal() {
       return ordinal;
    }

    /** creating is only possible in subclasses */
    protected Enum() { };

    /** get the String representation */
    public String toString() { return name(); }

    /** do not support cloning */
    protected final java.lang.Object clone() throws java.lang.CloneNotSupportedException
    { throw new CloneNotSupportedException(); }

}
