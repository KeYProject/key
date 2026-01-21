// This file is part of the RECODER library and protected by the LGPL.

package recoder.java.declaration.modifier;

import recoder.java.SourceVisitor;
import recoder.java.declaration.Modifier;

/**
 * Final.
 *
 * @author <TT>AutoDoc</TT>
 */

public class Final extends Modifier {

    /**
     * serialization id
     */
    private static final long serialVersionUID = 7169854150660337404L;

    /**
     * Final.
     */

    public Final() {
        // nothing to do
    }

    /**
     * Final.
     *
     * @param proto a final.
     */

    protected Final(Final proto) {
        super(proto);
    }

    /**
     * Deep clone.
     *
     * @return the object.
     */

    public Final deepClone() {
        return new Final(this);
    }

    public void accept(SourceVisitor v) {
        v.visitFinal(this);
    }
}
