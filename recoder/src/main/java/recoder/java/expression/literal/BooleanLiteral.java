/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.java.expression.literal;

import recoder.java.SourceVisitor;
import recoder.java.expression.Literal;

/**
 * Boolean literal.
 *
 * @author <TT>AutoDoc</TT>
 */

public class BooleanLiteral extends Literal {

    /**
     * serialization id
     */
    private static final long serialVersionUID = 1135231084094020816L;
    protected boolean value;

    /**
     * Boolean literal.
     */

    public BooleanLiteral() {
        // nothing to do
    }

    /**
     * Boolean literal.
     *
     * @param value a boolean value.
     */

    public BooleanLiteral(boolean value) {
        setValue(value);
    }

    /**
     * Boolean literal.
     *
     * @param value a string.
     */

    protected BooleanLiteral(String value) {
        if ("true".equals(value)) {
            setValue(true);
        } else if ("false".equals(value)) {
            setValue(false);
        } else {
            throw new IllegalArgumentException("Bad boolean literal " + value);
        }
    }

    /**
     * Boolean literal.
     *
     * @param proto a boolean literal.
     */

    protected BooleanLiteral(BooleanLiteral proto) {
        super(proto);
        value = proto.value;
    }

    /**
     * Deep clone.
     *
     * @return the object.
     */

    public BooleanLiteral deepClone() {
        return new BooleanLiteral(this);
    }

    /**
     * Get value.
     *
     * @return the string.
     */

    public boolean getValue() {
        return value;
    }

    /**
     * Set value.
     *
     * @param b a boolean value.
     */

    public void setValue(boolean b) {
        value = b;
    }

    public void accept(SourceVisitor v) {
        v.visitBooleanLiteral(this);
    }

    public Object getEquivalentJavaType() {
        return value;
    }
}
