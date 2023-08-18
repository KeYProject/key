/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.expression.literal;

import de.uka.ilkd.key.java.NameAbstractionTable;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.PrimitiveType;
import de.uka.ilkd.key.java.expression.Literal;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.ldt.DoubleLDT;
import de.uka.ilkd.key.logic.Name;

import org.key_project.util.ExtList;

/**
 * Double literal.
 *
 * @author <TT>AutoDoc</TT>
 */

public class DoubleLiteral extends Literal {

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
     * @param value a double value.
     */

    public DoubleLiteral(double value) {
        this.value = String.valueOf(value);
    }

    /**
     * Double literal.
     *
     * @param children list with all children(here:comments) May contain: Comments
     * @param value a string.
     */

    public DoubleLiteral(ExtList children, String value) {
        super(children);
        this.value = value;
    }

    /**
     * Double literal.
     *
     * @param value a string.
     */

    public DoubleLiteral(String value) {
        this.value = value;
    }

    /**
     * tests if equals
     */
    public boolean equalsModRenaming(SourceElement o, NameAbstractionTable nat) {
        if (!(o instanceof DoubleLiteral)) {
            return false;
        }
        return ((DoubleLiteral) o).getValue().equals(getValue());
    }

    @Override
    protected int computeHashCode() {
        return 37 * super.computeHashCode() + getValue().hashCode();
    }

    public boolean equals(Object o) {
        return super.equals(o);
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
