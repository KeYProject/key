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
import de.uka.ilkd.key.ldt.RealLDT;
import de.uka.ilkd.key.logic.Name;

import org.key_project.util.ExtList;

/**
 * JML \real literal.
 *
 * @author bruns
 */

public class RealLiteral extends Literal {

    /**
     * Textual representation of the value.
     */

    protected final String value;

    /**
     * Double literal.
     */

    public RealLiteral() {
        this.value = "0.0";
    }

    public RealLiteral(int value) {
        this(value + ".0");
    }

    public RealLiteral(double value) {
        this.value = String.valueOf(value);
    }

    public RealLiteral(java.math.BigDecimal value) {
        this.value = String.valueOf(value);
    }

    public RealLiteral(ExtList children, String value) {
        super(children);
        this.value = value;
    }

    public RealLiteral(ExtList children) {
        super(children);
        value = "0.0";
    }

    /**
     * Double literal.
     *
     * @param value a string.
     */

    public RealLiteral(String value) {
        this.value = value;
    }

    /**
     * tests if equals
     */
    public boolean equalsModRenaming(SourceElement o, NameAbstractionTable nat) {
        if (!(o instanceof RealLiteral)) {
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
