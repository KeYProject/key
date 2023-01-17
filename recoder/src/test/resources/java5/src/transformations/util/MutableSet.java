// This file is part of the RECODER library and protected by the LGPL.

package recoder.util;

/**
 * @author AL
 */
public interface MutableSet extends Set {

    Object add(Object key);

    Object remove(Object key);

    /**
     * Removes an arbitrary object of the set, if there is one left.
     * 
     * @return a former element of the set, or <CODE>null</CODE> if the set
     *         was empty.
     */
    Object removeAny();

    void clear();

    void join(Set set);

    void intersect(Set set);

    void subtract(Set set);
}