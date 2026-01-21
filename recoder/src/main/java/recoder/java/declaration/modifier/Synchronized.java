// This file is part of the RECODER library and protected by the LGPL.

package recoder.java.declaration.modifier;

import recoder.java.SourceVisitor;
import recoder.java.declaration.Modifier;

/**
 * Synchronized.
 *
 * @author <TT>AutoDoc</TT>
 */

public class Synchronized extends Modifier {

    /**
     * serialization id
     */
    private static final long serialVersionUID = -4425302603634609276L;

    /**
     * Synchronized.
     */

    public Synchronized() {
        // nothing to do
    }

    /**
     * Synchronized.
     *
     * @param proto a synchronized.
     */

    protected Synchronized(Synchronized proto) {
        super(proto);
    }

    /**
     * Deep clone.
     *
     * @return the object.
     */

    public Synchronized deepClone() {
        return new Synchronized(this);
    }

    public void accept(SourceVisitor v) {
        v.visitSynchronized(this);
    }

}
