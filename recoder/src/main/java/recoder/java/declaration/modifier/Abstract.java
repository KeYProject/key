// This file is part of the RECODER library and protected by the LGPL.

package recoder.java.declaration.modifier;

import recoder.java.SourceVisitor;
import recoder.java.declaration.Modifier;

/**
 * Abstract.
 *
 * @author <TT>AutoDoc</TT>
 */

public class Abstract extends Modifier {

    /**
     * serialization id
     */
    private static final long serialVersionUID = -380790417611526476L;

    /**
     * Abstract.
     */

    public Abstract() {
        // nothing to do
    }

    /**
     * Abstract.
     *
     * @param proto an abstract.
     */

    protected Abstract(Abstract proto) {
        super(proto);
    }

    /**
     * Deep clone.
     *
     * @return the object.
     */

    public Abstract deepClone() {
        return new Abstract(this);
    }

    public void accept(SourceVisitor v) {
        v.visitAbstract(this);
    }
}
