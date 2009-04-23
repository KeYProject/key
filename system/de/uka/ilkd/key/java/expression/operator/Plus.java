// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//


package de.uka.ilkd.key.java.expression.operator;

import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.PrettyPrinter;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.util.ExtList;

/**
 *  Addition or string concatenation operator "+".
 */

public class Plus extends BinaryOperator {


    /**
     * Constructor for the transformation of COMPOST ASTs to KeY.
     * The first occurrence of an Expression in the given list is taken as
     * the left hand side 
     * of the expression, the second occurrence is taken as the right hand
     * side of the expression.
     * @param children the children of this AST element as KeY classes.
     */
    public Plus(ExtList children) {
	super(children);
    }

    public Plus(Expression lhs, Expression rhs) {
	super(lhs, rhs);
    }


    /**
     *      Get precedence.
     *      @return the int value.
     */

    public int getPrecedence() {
        return 3;
    }

    /**
     *      Get notation.
     *      @return the int value.
     */
    public int getNotation() {
        return INFIX;
    }


    /** calls the corresponding method of a visitor in order to
     * perform some action/transformation on this element
     * @param v the Visitor
     */
    public void visit(Visitor v) {
	v.performActionOnPlus(this);
    }

    public void prettyPrint(PrettyPrinter p) throws java.io.IOException {
        p.printPlus(this);
    }
}
