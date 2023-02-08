/* This file is part of KeY - https://key-project.org
 * KeY is licensed by the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0 */
package de.uka.ilkd.key.java.statement;

import org.key_project.util.ExtList;

import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.PrettyPrinter;
import de.uka.ilkd.key.java.visitor.Visitor;

/**
 * Throw.
 */

public class Throw extends ExpressionJumpStatement {

    /**
     * Throw.
     */

    public Throw() {}

    /**
     * Throw.
     *
     * @param expr an expression.
     */

    public Throw(Expression expr) {
        super(expr);
        if (expr == null) {
            throw new IllegalArgumentException("Throw requires one argument");
        }
    }

    /**
     * Throw.
     *
     * @param children an ExtList with all children
     */

    public Throw(ExtList children) {
        super(children);
    }

    /**
     * calls the corresponding method of a visitor in order to perform some action/transformation on
     * this element
     *
     * @param v the Visitor
     */
    public void visit(Visitor v) {
        v.performActionOnThrow(this);
    }

    public void prettyPrint(PrettyPrinter p) throws java.io.IOException {
        p.printThrow(this);
    }
}
