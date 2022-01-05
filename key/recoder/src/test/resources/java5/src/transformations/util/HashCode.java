// This file is part of the RECODER library and protected by the LGPL.

package recoder.util;

/**
 * This interface defines a function mapping objects to integer values. The
 * integer code is used for hashing algorithms and must obey the constraint
 * <BLOCKQUOTE><CODE>equals(x,&nbsp;y)</CODE> implies <CODE>
 * hashCode(x)&nbsp;==&nbsp;hashCode(y)</CODE>. </BLOCKQUOTE> Therefore, this
 * interface extends that equality relation. The value returned by <CODE>
 * hashCode</CODE> does not need to be a unique value, but should be different
 * for most different objects to achieve adequate performance. Whether or not
 * <CODE>null</CODE> objects are allowed is up to the specific implementation.
 * 
 * @author AL
 */
public interface HashCode extends Equality {

    /**
     * Return an integer value representing the object.
     * 
     * @param x
     *            an object.
     * @return the hash code.
     */
    int hashCode(Object x);

    /**
     * Natural hash code implementation. This object calls and returns <TT>
     * x.hashCode()</TT> and therefore does not allow <CODE>null</CODE>
     * objects.
     */
    HashCode NATURAL = new Order.Natural();

    /**
     * Identity hash code implementation. This object calls <CODE>
     * System.identityHashCode(x)</CODE> which will report zero for <CODE>null
     * </CODE> objects.
     */
    HashCode IDENTITY = new Order.Identity();
}