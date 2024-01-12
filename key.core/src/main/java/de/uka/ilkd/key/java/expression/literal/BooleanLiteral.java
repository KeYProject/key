/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.expression.literal;

import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.PrimitiveType;
import de.uka.ilkd.key.java.expression.Literal;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.ldt.BooleanLDT;
import de.uka.ilkd.key.logic.Name;

import org.key_project.util.ExtList;


/**
 * Boolean literal.
 *
 * @author <TT>AutoDoc</TT>
 */
public class BooleanLiteral extends Literal {

    public final static BooleanLiteral TRUE = new BooleanLiteral(true);
    public final static BooleanLiteral FALSE = new BooleanLiteral(false);


    protected final boolean value;


    /**
     * get boolean literal for the given <code>value</code>. This supports use of single literals,
     * but we do not force it.
     *
     * @param val a boolean specifying the literal to be returned
     * @return the BooleanLiteral representing <tt>val</tt>
     */
    public static BooleanLiteral getBooleanLiteral(boolean val) {
        return val ? TRUE : FALSE;
    }

    /**
     * Boolean literal.
     *
     * @param value a boolean value.
     */

    private BooleanLiteral(boolean value) {
        this.value = value;
    }

    /**
     * Boolean literal.
     *
     * @param children list with all children May contain: Comments
     * @param value a boolean value.
     */
    public BooleanLiteral(ExtList children, boolean value) {
        super(children);
        this.value = value;
    }

    /**
     * Boolean literal.
     *
     * @param children list with all children
     * @param pos The source code position.
     * @param value a boolean value.
     */
    public BooleanLiteral(ExtList children, PositionInfo pos, boolean value) {
        super(children, pos);
        this.value = value;
    }

    /**
     * Boolean literal.
     *
     * @param pos The source code position.
     * @param value a boolean value.
     */
    public BooleanLiteral(PositionInfo pos, boolean value) {
        super(pos);
        this.value = value;
    }

    /**
     * Get value.
     *
     * @return the string.
     */

    public boolean getValue() {
        return value;
    }

    /**
     * Get value.
     *
     * @return the string.
     */

    public String getName() {
        return (value ? "true" : "false");
    }

    /**
     * tests if equals
     */
    public boolean equalsModRenaming(SourceElement o, NameAbstractionTable nat) {
        if (!(o instanceof BooleanLiteral)) {
            return false;
        }
        return ((BooleanLiteral) o).getValue() == getValue();
    }

    @Override
    protected int computeHashCode() {
        return 37 * super.computeHashCode() + (getValue() ? 0 : 1);
    }

    @Override
    public boolean equals(Object o) {
        return super.equals(o);
    }

    /**
     * calls the corresponding method of a visitor in order to perform some action/transformation on
     * this element
     *
     * @param v the Visitor
     */
    public void visit(Visitor v) {
        v.performActionOnBooleanLiteral(this);
    }


    public KeYJavaType getKeYJavaType(Services javaServ) {
        return javaServ.getJavaInfo().getKeYJavaType(PrimitiveType.JAVA_BOOLEAN);
    }

    @Override
    public Name getLDTName() {
        return BooleanLDT.NAME;
    }

}
