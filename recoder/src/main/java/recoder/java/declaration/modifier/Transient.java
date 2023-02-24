// This file is part of the RECODER library and protected by the LGPL.

package recoder.java.declaration.modifier;

import recoder.java.SourceVisitor;
import recoder.java.declaration.Modifier;

/**
 * Transient.
 *
 * @author <TT>AutoDoc</TT>
 */

public class Transient extends Modifier {

    /**
     * serialization id
     */
    private static final long serialVersionUID = 3518754803226194289L;

    /**
     * Transient.
     */

    public Transient() {
        // nothing to do
    }

    /**
     * Transient.
     *
     * @param proto a transient.
     */

    protected Transient(Transient proto) {
        super(proto);
    }

    /**
     * Deep clone.
     *
     * @return the object.
     */

    public Transient deepClone() {
        return new Transient(this);
    }

    public void accept(SourceVisitor v) {
        v.visitTransient(this);
    }
}
