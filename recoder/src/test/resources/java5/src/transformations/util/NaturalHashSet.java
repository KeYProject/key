// This file is part of the RECODER library and protected by the LGPL.

package recoder.util;

/**
 * @author AL
 */
public class NaturalHashSet extends AbstractHashSet {

    public NaturalHashSet() {
        super();
    }

    public NaturalHashSet(int initialCapacity) {
        super(initialCapacity);
    }

    public final int hashCode(Object o) {
        return o.hashCode();
    }

    public final boolean equals(Object p, Object q) {
        return p.equals(q);
    }
}