// This file is part of the RECODER library and protected by the LGPL.

package recoder.util;

import java.util.HashSet;
import java.util.Set;

// to do: make Serializable

/**
 * Implements an unary predicate over objects. Implemented as simple marker (external boolean flag),
 * that can be used to mark objects. This may be required e.g. for graph traversals.
 *
 * @author RN
 */
public class Marker implements Cloneable {

    private final Set<Object> marks = new HashSet<>();

    public void mark(Object o) {
        marks.add(o);
    }

    public void unmark(Object o) {
        marks.remove(o);
    }

    public boolean isMarked(Object o) {
        return marks.contains(o);
    }

}
