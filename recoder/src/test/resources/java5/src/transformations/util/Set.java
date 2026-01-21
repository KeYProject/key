// This file is part of the RECODER library and protected by the LGPL.

package recoder.util;

import java.util.Enumeration;

/**
 * @author AL
 */
public interface Set {

    int size();

    boolean isEmpty();

    Enumeration elements();

    boolean contains(Object key);

    Object get(Object key);

    Set EMPTY_SET = new NaturalHashSet();
    // should be a special implementation that cannot be casted and modified
}