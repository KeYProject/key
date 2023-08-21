/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.java.expression.literal;

import recoder.java.SourceVisitor;
import recoder.java.expression.Literal;

/**
 * Int literal.
 *
 * @author <TT>AutoDoc</TT>
 */

public class IntLiteral extends Literal {

    /**
     * serialization id
     */
    private static final long serialVersionUID = -5285529378094375335L;

    /**
     * Textual representation of the value.
     */

    protected String value;

    /**
     * Int literal.
     */

    public IntLiteral() {
        setValue("0");
    }

    /**
     * Int literal.
     *
     * @param value an int value.
     */

    public IntLiteral(int value) {
        setValue("" + value);
    }

    /**
     * Int literal.
     *
     * @param value a string.
     */

    public IntLiteral(String value) {
        setValue(value);
    }

    /**
     * Int literal.
     *
     * @param proto an int literal.
     */

    protected IntLiteral(IntLiteral proto) {
        super(proto);
        value = proto.value;
    }

    /**
     * Deep clone.
     *
     * @return the object.
     */

    public IntLiteral deepClone() {
        return new IntLiteral(this);
    }

    /**
     * Get value.
     *
     * @return the string.
     */

    public String getValue() {
        return value;
    }

    /**
     * Set value.
     *
     * @param str a string value.
     */

    public void setValue(String str) {
        // unchecked
        this.value = str.intern();
    }

    public void accept(SourceVisitor v) {
        v.visitIntLiteral(this);
    }

    public Object getEquivalentJavaType() {
        return Integer.valueOf(value);
    }
}
