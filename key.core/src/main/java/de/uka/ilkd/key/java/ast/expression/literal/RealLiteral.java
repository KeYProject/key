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
import de.uka.ilkd.key.ldt.RealLDT;
import org.jspecify.annotations.Nullable;
import org.key_project.logic.Name;

import java.util.List;

/**
 * JML \real literal.
 *
 * @author bruns
 */
public final class RealLiteral extends Literal {

    /**
     * Textual representation of the value.
     */
    private final String value;

    /**
     * Double literal.
     */
    public RealLiteral() {
        this(null, null, "0.0");
    }

    public RealLiteral(int value) {
        this(null, null, value + ".0");
    }

    public RealLiteral(double value) {
        this(null, null, String.valueOf(value));
    }

    public RealLiteral(java.math.BigDecimal value) {
        this(null, null, String.valueOf(value));
    }

    public RealLiteral(@Nullable PositionInfo pi, @Nullable List<Comment> c, String value) {
        super(pi, c);
        this.value = value;
    }

    /**
     * Double literal.
     *
     * @param value a string.
     */
    public RealLiteral(String value) {
        this(null, null, value);
    }

    @Override
    public boolean equals(Object o) {
        if (o == this) {
            return true;
        }
        if (o == null || o.getClass() != this.getClass()) {
            return false;
        }
        return ((RealLiteral) o).getValue().equals(getValue());
    }

    @Override
    public int computeHashCode() {
        return 17 * super.computeHashCode() + getValue().hashCode();
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
        // v.performActionOnDoubleLiteral(this);
    }

    public KeYJavaType getKeYJavaType(Services javaServ) {
        return javaServ.getJavaInfo().getKeYJavaType(PrimitiveType.JAVA_REAL);
    }

    @Override
    public Name getLDTName() {
        return RealLDT.NAME;
    }

}
