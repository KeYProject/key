// This file is part of the RECODER library and protected by the LGPL.

package recoder.util;

// to do: make Serializable

/**
 * Implements an unary predicate over objects. Implemented as simple marker
 * (external boolean flag), that can be used to mark objects. This may be
 * required e.g. for graph traversals.
 * 
 * @author RN
 */
public class Marker implements Cloneable {

    private MutableSet marks = new IdentityHashSet();

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