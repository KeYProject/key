// This file is part of the RECODER library and protected by the LGPL.

package recoder.util;

import java.util.Enumeration;

/**
 * @author AL
 */
public interface Map {

    int size();

    boolean isEmpty();

    Enumeration keys();

    Enumeration elements();

    boolean contains(Object value);

    boolean containsKey(Object key);

    Object get(Object key);

    Map EMPTY_MAP = new NaturalHashTable();
    // should be a special implementation that cannot be casted and modified
}