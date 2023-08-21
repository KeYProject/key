/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.java.expression.literal;

import recoder.java.SourceVisitor;
import recoder.java.expression.Literal;

/**
 * Double literal.
 *
 * @author <TT>AutoDoc</TT>
 */

public class DoubleLiteral extends Literal {

    /**
     * serialization id
     */
    private static final long serialVersionUID = 6628200854323360553L;
    /**
     * Textual representation of the value.
     */

    protected String value;

    /**
     * Double literal.
     */

    public DoubleLiteral() {
        setValue("0.0");
    }

    /**
     * Double literal.
     *
     * @param value a double value.
     */

    public DoubleLiteral(double value) {
        setValue("" + value);
    }

    /**
     * Double literal.
     *
     * @param value a string.
     */

    public DoubleLiteral(String value) {
        setValue(value);
    }

    /**
     * Double literal.
     *
     * @param proto a double literal.
     */

    protected DoubleLiteral(DoubleLiteral proto) {
        super(proto);
        value = proto.value;
    }

    /**
     * Deep clone.
     *
     * @return the object.
     */

    public DoubleLiteral deepClone() {
        return new DoubleLiteral(this);
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
        v.visitDoubleLiteral(this);
    }

    public Object getEquivalentJavaType() {
        return Double.valueOf(value);
    }
}
