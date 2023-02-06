// This file is part of the RECODER library and protected by the LGPL.

package recoder.java.declaration.modifier;

import recoder.java.SourceVisitor;
import recoder.java.declaration.Modifier;

/**
 * Static.
 *
 * @author <TT>AutoDoc</TT>
 */

public class Static extends Modifier {

    /**
     * serialization id
     */
    private static final long serialVersionUID = -6125238838094732013L;

    /**
     * Static.
     */

    public Static() {
        // nothing to do
    }

    /**
     * Static.
     *
     * @param proto a static.
     */

    protected Static(Static proto) {
        super(proto);
    }

    /**
     * Deep clone.
     *
     * @return the object.
     */

    public Static deepClone() {
        return new Static(this);
    }

    public void accept(SourceVisitor v) {
        v.visitStatic(this);
    }
}
