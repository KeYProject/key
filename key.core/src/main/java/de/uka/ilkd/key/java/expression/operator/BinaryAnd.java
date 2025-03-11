/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.expression.operator;

import de.uka.ilkd.key.java.visitor.Visitor;

import org.key_project.util.ExtList;

/**
 * Binary and.
 */

public class BinaryAnd extends BinaryOperator {

    /**
     * Binary and.
     *
     * @param children an ExtList with all children of this node the first children in list will be
     *        the one on the left side, the second the one on the right side.
     */

    public BinaryAnd(ExtList children) {
        super(children);
    }

    /**
     * Get arity.
     *
     * @return the int value.
     */

    public final int getArity() {
        return 2;
    }

    /**
     * Get precedence.
     *
     * @return the int value.
     */

    public final int getPrecedence() {
        return 7;
    }

    /**
     * Get notation.
     *
     * @return the int value.
     */

    public final int getNotation() {
        return INFIX;
    }

    /**
     * calls the corresponding method of a visitor in order to perform some action/transformation on
     * this element
     *
     * @param v the Visitor
     */
    public void visit(Visitor v) {
        v.performActionOnBinaryAnd(this);
    }


}
