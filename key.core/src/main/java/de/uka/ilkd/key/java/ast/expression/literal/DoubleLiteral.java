/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.ast.expression.literal;

import java.util.List;

import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.ast.Comment;
import de.uka.ilkd.key.java.ast.PositionInfo;
import de.uka.ilkd.key.java.ast.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.ast.abstraction.PrimitiveType;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.ldt.DoubleLDT;

import org.key_project.logic.Name;
import org.key_project.util.ExtList;

/**
 * Double literal.
 *
 * @author <TT>AutoDoc</TT>
 */

public non-sealed class DoubleLiteral extends Literal {

    /**
     * Textual representation of the value.
     */

    protected final String value;

    /**
     * Double literal.
     */

    public DoubleLiteral() {
        this.value = "0.0";
    }

    /**
     * Double literal.
     *
     * @param value
     *        a double value.
     */

    public DoubleLiteral(double value) {
        this.value = String.valueOf(value);
    }

    /**
     * Double literal.
     *
     * @param children
     *        list with all children(here:comments) May contain: Comments
     * @param value
     *        a string.
     */

    public DoubleLiteral(ExtList children, String value) {
        super(children);
        this.value = value;
    }

    /**
     * Double literal.
     *
     * @param value
     *        a string.
     */

    public DoubleLiteral(String value) {
        this.value = value;
    }

    public DoubleLiteral(PositionInfo pi, List<Comment> c, String value) {
        super(pi, c);
        this.value = value;
    }


    @Override
    public boolean equals(Object o) {
        if (o == this) { return true; }
        if (o == null || o.getClass() != this.getClass()) { return false; }
        return ((DoubleLiteral) o).getValue().equals(getValue());
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
     * @param v
     *        the Visitor
     */
    public void visit(Visitor v) {
        v.performActionOnDoubleLiteral(this);
    }

    public KeYJavaType getKeYJavaType(Services javaServ) {
        return javaServ.getJavaInfo().getKeYJavaType(PrimitiveType.JAVA_DOUBLE);
    }

    @Override
    public Name getLDTName() {
        return DoubleLDT.NAME;
    }

}
