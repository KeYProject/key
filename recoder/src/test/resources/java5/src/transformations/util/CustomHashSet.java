// This file is part of the RECODER library and protected by the LGPL.

package recoder.util;

/**
 * @author AL
 */
public class CustomHashSet extends AbstractHashSet {

    private HashCode hasher;

    public CustomHashSet(HashCode hasher) {
        super();
        setHashCode(hasher);
    }

    public CustomHashSet(int initialCapacity, HashCode hasher) {
        super(initialCapacity);
        setHashCode(hasher);
    }

    protected void setHashCode(HashCode hasher) {
        if (hasher == null) {
            throw new IllegalArgumentException("Null hash code function");
        }
        this.hasher = hasher;
    }

    public final int hashCode(Object o) {
        return hasher.hashCode(o);
    }

    public final boolean equals(Object p, Object q) {
        return hasher.equals(p, q);
    }
}