// This file is part of the RECODER library and protected by the LGPL.

package recoder.util;

/**
 * @author AL
 */
public class IdentityIndex extends AbstractIndex {

    public IdentityIndex() {
        super();
    }

    public IdentityIndex(int initialCapacity) {
        super(initialCapacity);
    }

    public final int hashCode(Object o) {
        return System.identityHashCode(o);
    }

    public final boolean equals(Object p, Object q) {
        return p == q;
    }
}