/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.ast.expression.literal;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.ast.Comment;
import de.uka.ilkd.key.java.ast.PositionInfo;
import de.uka.ilkd.key.java.ast.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.ast.abstraction.PrimitiveType;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.ldt.FloatLDT;
import org.jspecify.annotations.Nullable;
import org.key_project.logic.Name;

import java.util.List;

/**
 * Float literal.
 *
 * @author <TT>AutoDoc</TT>
 */

public non-sealed class FloatLiteral extends Literal {
    /**
     * Textual representation of the value.
     */
    protected final String value;

    /**
     * Float literal.
     *
     * @param value a float value.
     */
    public FloatLiteral(float value) {
        this(String.valueOf(value));
    }

    /**
     * Float literal.
     *
     * @param value a string.
     */
    public FloatLiteral(String value) {
        this(null, null, value);
    }

    public FloatLiteral(@Nullable PositionInfo pi, @Nullable List<Comment> c, String value) {
        super(pi, c);
        this.value = value;
    }

    @Override
    public boolean equals(Object o) {
        if (o == this) {
            return true;
        }
        if (o == null || o.getClass() != this.getClass()) {
            return false;
        }
        return ((FloatLiteral) o).getValue().equals(getValue());
    }

    @Override
    protected int computeHashCode() {
        return 37 * super.computeHashCode() + getValue().hashCode();
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
     * calls the corresponding method of a visitor in order to perform some action/transformation on
     * this element
     *
     * @param v the Visitor
     */
    public void visit(Visitor v) {
        v.performActionOnFloatLiteral(this);
    }

    public KeYJavaType getKeYJavaType(Services javaServ) {
        return javaServ.getJavaInfo().getKeYJavaType(PrimitiveType.JAVA_FLOAT);
    }

    @Override
    public Name getLDTName() {
        return FloatLDT.NAME;
    }

}
