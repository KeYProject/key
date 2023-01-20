// This file is part of the RECODER library and protected by the LGPL.

package recoder.util;

/**
 * This interface defines an equality relation between two objects. Equality
 * relations are
 * <UL>
 * <LI><I>reflexive </I> <BR>
 * <CODE>equals(x,&nbsp;x)</CODE></LI>
 * <LI><I>symmetric </I> <BR>
 * <CODE>equals(x,&nbsp;y)&nbsp;==&nbsp;equals(y,&nbsp;x)</CODE></LI>
 * <LI><I>transitive </I> <BR>
 * <CODE>(equals(x,&nbsp;y)&nbsp;&&&nbsp;equals(y,&nbsp;z))</CODE> implies
 * <CODE>equals(x,&nbsp;z)</CODE></LI>
 * </UL>
 * Whether or not objects of different type or <CODE>null</CODE> objects are
 * allowed is up to the specific implementation.
 * 
 * @author AL
 */
public interface Equality {

    /**
     * Compares two objects for equality.
     * 
     * @param x
     *            the first object.
     * @param y
     *            the second object.
     * @return true, if x equals y, false otherwise.
     */
    boolean equals(Object x, Object y);

    /**
     * Natural equality relation object. The implementation calls x.equals(y),
     * hence no <CODE>null</CODE> are allowed (not even for y, as the relation
     * must be symmetric).
     */
    Equality NATURAL = Order.NATURAL;

    /**
     * Identity equality relation object. The implementation compares x and y
     * for object identity (x&nbsp;==&nbsp;y). Two <CODE>null</CODE> objects
     * are considered equal.
     */
    Equality IDENTITY = Order.IDENTITY;
}