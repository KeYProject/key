/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.java.expression.literal;

import recoder.java.NonTerminalProgramElement;
import recoder.java.SourceVisitor;
import recoder.java.expression.Literal;
import recoder.java.reference.ReferencePrefix;
import recoder.java.reference.ReferenceSuffix;

/**
 * String literal.
 *
 * @author <TT>AutoDoc</TT>
 */

public class StringLiteral extends Literal implements ReferencePrefix {

    /**
     * serialization id
     */
    private static final long serialVersionUID = 7368137274068211543L;

    /**
     * Reference parent.
     */

    protected ReferenceSuffix referenceParent;

    /**
     * The value.
     */

    protected String value;

    /**
     * String literal.
     */

    public StringLiteral() {
        setValue("");
    }

    /**
     * String literal.
     *
     * @param value a string.
     */

    public StringLiteral(String value) {
        setValue(value);
    }

    /**
     * String literal.
     *
     * @param proto a string literal.
     */

    protected StringLiteral(StringLiteral proto) {
        super(proto);
        value = proto.value;
    }

    /**
     * Deep clone.
     *
     * @return the object.
     */

    public StringLiteral deepClone() {
        return new StringLiteral(this);
    }

    /**
     * Get AST parent.
     *
     * @return the non terminal program element.
     */

    public NonTerminalProgramElement getASTParent() {
        if (expressionParent != null) {
            return expressionParent;
        } else {
            return referenceParent;
        }
    }

    /**
     * Get reference suffix.
     *
     * @return the reference suffix.
     */

    public ReferenceSuffix getReferenceSuffix() {
        return referenceParent;
    }

    /**
     * Set reference suffix.
     *
     * @param path a reference suffix.
     */

    public void setReferenceSuffix(ReferenceSuffix path) {
        referenceParent = path;
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
        if (!str.startsWith("\"") || !str.endsWith("\"")) {
            throw new IllegalArgumentException("Bad string literal " + value);
        }
        this.value = str.intern();
    }

    public void accept(SourceVisitor v) {
        v.visitStringLiteral(this);
    }

    public Object getEquivalentJavaType() {
        return value;
    }
}
