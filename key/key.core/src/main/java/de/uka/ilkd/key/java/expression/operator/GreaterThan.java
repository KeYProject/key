// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.java.expression.operator;

import org.key_project.util.ExtList;

import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.PrettyPrinter;
import de.uka.ilkd.key.java.visitor.Visitor;

/**
 *  Greater than.
 */

public class GreaterThan extends ComparativeOperator {


    /**
     *      Greater than.
     *      @param children an ExtList with all children of this node
     *      the first children in list will be the one on the left
     *      side, the second the one on the  right side.
     */

    public GreaterThan(ExtList children) {
        super(children);
    }

    /**
     * Greater than.
     * @param lhs the expression that is checked to be greater than rhs
     * @param rhs the expression that is checked to be less than lhs
     */
    public GreaterThan(Expression lhs, Expression rhs) {
        super(lhs, rhs);
    }

    /**
 *      Get precedence.
 *      @return the int value.
     */

    public int getPrecedence() {
        return 5;
    }

    /** calls the corresponding method of a visitor in order to
     * perform some action/transformation on this element
     * @param v the Visitor
     */
    public void visit(Visitor v) {
	v.performActionOnGreaterThan(this);
    }

    public void prettyPrint(PrettyPrinter p) throws java.io.IOException {
        p.printGreaterThan(this);
    }
}