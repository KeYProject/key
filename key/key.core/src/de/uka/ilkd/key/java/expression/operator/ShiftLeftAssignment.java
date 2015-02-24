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

import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.PrettyPrinter;
import de.uka.ilkd.key.java.expression.Assignment;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.util.ExtList;

/**
 *  Shift left assignment.
 *  
 */

public class ShiftLeftAssignment extends Assignment {

    /**
     *      Shift left assignment.
     */

    public ShiftLeftAssignment() {}

    /**
     *      Shift left assignment.
     *      @param lhs an expression.
     *      @param rhs an expression.
     */

    public ShiftLeftAssignment(Expression lhs, Expression rhs) {
        super(lhs, rhs);
    }

    /**
     * Constructor for the transformation of COMPOST ASTs to KeY.
     * The first occurrence of an Expression in the given list is taken as
     * the left hand side 
     * of the expression, the second occurrence is taken as the right hand
     * side of the expression.
     * @param children the children of this AST element as KeY classes.
     */
    public ShiftLeftAssignment(ExtList children) {
	super(children);
    }


    /**
     *      Get arity.
     *      @return the int value.
     */

    public int getArity() {
        return 2;
    }

    /**
     *      Get precedence.
     *      @return the int value.
     */

    public int getPrecedence() {
        return 13;
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
	v.performActionOnShiftLeftAssignment(this);
    }

    public void prettyPrint(PrettyPrinter p) throws java.io.IOException {
        p.printShiftLeftAssignment(this);
    }
}