/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.java.expression.literal;

import recoder.java.SourceVisitor;
import recoder.java.expression.Literal;

/**
 * Float literal.
 *
 * @author <TT>AutoDoc</TT>
 */

public class FloatLiteral extends Literal {

    /**
     * serialization id
     */
    private static final long serialVersionUID = 9215865599908556320L;

    /**
     * Textual representation of the value.
     */

    protected String value;

    /**
     * Float literal.
     */

    public FloatLiteral() {
        setValue("0.0F");
    }

    /**
     * Float literal.
     *
     * @param value a float value.
     */

    public FloatLiteral(float value) {
        setValue("" + value + 'F');
    }

    /**
     * Float literal.
     *
     * @param value a string.
     */

    public FloatLiteral(String value) {
        setValue((value.endsWith("F") || value.endsWith("f")) ? value : (value + 'F'));
    }

    /**
     * Float literal.
     *
     * @param proto a float literal.
     */

    protected FloatLiteral(FloatLiteral proto) {
        super(proto);
        value = proto.value;
    }

    /**
     * Deep clone.
     *
     * @return the object.
     */

    public FloatLiteral deepClone() {
        return new FloatLiteral(this);
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
        v.visitFloatLiteral(this);
    }

    public Object getEquivalentJavaType() {
        return Float.valueOf(value);
    }
}
