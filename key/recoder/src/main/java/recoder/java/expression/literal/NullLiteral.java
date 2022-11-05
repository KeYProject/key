// This file is part of the RECODER library and protected by the LGPL.

package recoder.java.expression.literal;

import recoder.java.SourceVisitor;
import recoder.java.expression.Literal;

/**
 * Null literal.
 *
 * @author <TT>AutoDoc</TT>
 */

public class NullLiteral extends Literal {

    /**
     * serialization id
     */
    private static final long serialVersionUID = -1679522775179075816L;

    /**
     * Null literal.
     */

    public NullLiteral() {
        // nothing to do
    }

    /**
     * Null literal.
     *
     * @param proto a null literal.
     */

    protected NullLiteral(NullLiteral proto) {
        super(proto);
    }

    /**
     * Deep clone.
     *
     * @return the object.
     */

    public NullLiteral deepClone() {
        return new NullLiteral(this);
    }

    public void accept(SourceVisitor v) {
        v.visitNullLiteral(this);
    }

    public Object getEquivalentJavaType() {
        return null;
    }
}
