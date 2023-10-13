/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.java.expression.literal;

import recoder.java.SourceVisitor;
import recoder.java.expression.Literal;

/**
 * Char literal.
 *
 * @author <TT>AutoDoc</TT>
 */

public class CharLiteral extends Literal {

    /**
     * serialization id
     */
    private static final long serialVersionUID = -558509934440205638L;
    protected String value;

    /**
     * Char literal.
     */

    public CharLiteral() {
        // nothing to do
    }

    /**
     * Char literal.
     *
     * @param value a char value.
     */

    public CharLiteral(char value) {
        setValue(value);
    }

    /**
     * Char literal.
     *
     * @param value a string.
     */

    public CharLiteral(String value) {
        setValue(value);
    }

    /**
     * Char literal.
     *
     * @param proto a char literal.
     */

    protected CharLiteral(CharLiteral proto) {
        super(proto);
        value = proto.value;
    }

    /**
     * Deep clone.
     *
     * @return the object.
     */

    public CharLiteral deepClone() {
        return new CharLiteral(this);
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
     * @param c a char value.
     */

    public void setValue(char c) {
        setValue("'" + c + "'");
    }

    /**
     * Set value.
     *
     * @param str a string value.
     */

    public void setValue(String str) {
        if (!str.startsWith("'") || !str.endsWith("'")) {
            throw new IllegalArgumentException("Bad char literal " + value);
        }
        this.value = str.intern();
    }

    public void accept(SourceVisitor v) {
        v.visitCharLiteral(this);
    }

    public Object getEquivalentJavaType() {
        return value.charAt(0);
    }
}
