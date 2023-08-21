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
import de.uka.ilkd.key.ldt.FloatLDT;
import de.uka.ilkd.key.logic.Name;

import org.key_project.util.ExtList;

/**
 * Float literal.
 *
 * @author <TT>AutoDoc</TT>
 */

public class FloatLiteral extends Literal {

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
        this.value = String.valueOf(value);
    }

    /**
     * Float literal.
     *
     * @param children an ExtList with all children(here:comments)
     * @param value a string.
     */

    public FloatLiteral(ExtList children, String value) {
        super(children);
        this.value = value;
    }

    /**
     * Float literal.
     *
     * @param value a string.
     */

    public FloatLiteral(String value) {
        this.value = value;
    }

    /**
     * tests if equals
     */
    public boolean equalsModRenaming(SourceElement o, NameAbstractionTable nat) {
        if (!(o instanceof FloatLiteral)) {
            return false;
        }
        return ((FloatLiteral) o).getValue().equals(getValue());
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
