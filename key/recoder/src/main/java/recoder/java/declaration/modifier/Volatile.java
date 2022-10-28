// This file is part of the RECODER library and protected by the LGPL.

package recoder.java.declaration.modifier;

import recoder.java.SourceVisitor;
import recoder.java.declaration.Modifier;

/**
 * Volatile.
 *
 * @author <TT>AutoDoc</TT>
 */

public class Volatile extends Modifier {

    /**
     * serialization id
     */
    private static final long serialVersionUID = -8915246411373317235L;

    /**
     * Volatile.
     */

    public Volatile() {
        // nothing to do
    }

    /**
     * Volatile.
     *
     * @param proto a volatile.
     */

    protected Volatile(Volatile proto) {
        super(proto);
    }

    /**
     * Deep clone.
     *
     * @return the object.
     */

    public Volatile deepClone() {
        return new Volatile(this);
    }

    public void accept(SourceVisitor v) {
        v.visitVolatile(this);
    }
}
