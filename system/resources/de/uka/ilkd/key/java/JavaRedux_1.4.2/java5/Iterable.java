package java.lang;

import java.util.Iterator;

/** Implementing this interface allows an object to be the target of
 *  the "foreach" statement.
 */
public interface Iterable {

    /**
     * Returns an iterator
     * @return an Iterator.
     */
    Iterator iterator();
}
