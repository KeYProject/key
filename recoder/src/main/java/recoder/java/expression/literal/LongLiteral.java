/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.java.expression.literal;

import recoder.java.SourceVisitor;
import recoder.java.expression.Literal;

/**
 * Long literal.
 *
 * @author <TT>AutoDoc</TT>
 */

public class LongLiteral extends Literal {

    /**
     * serialization id
     */
    private static final long serialVersionUID = -8507020453717633759L;

    /**
     * Textual representation of the value.
     */

    protected String value;

    /**
     * Long literal.
     */

    public LongLiteral() {
        setValue("0L");
    }

    /**
     * Long literal.
     *
     * @param value a long value.
     */

    public LongLiteral(long value) {
        setValue("" + value + 'L');
    }

    /**
     * Long literal.
     *
     * @param value a string.
     */

    public LongLiteral(String value) {
        setValue((value.endsWith("L") || value.endsWith("l")) ? value : (value + 'L'));
    }

    /**
     * Long literal.
     *
     * @param proto a long literal.
     */

    protected LongLiteral(LongLiteral proto) {
        super(proto);
        value = proto.value;
    }

    /**
     * Deep clone.
     *
     * @return the object.
     */

    public LongLiteral deepClone() {
        return new LongLiteral(this);
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
        v.visitLongLiteral(this);
    }

    public Object getEquivalentJavaType() {
        return Long.valueOf(value);
    }
}
