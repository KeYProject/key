/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
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
