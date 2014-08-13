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
 *  Copy assignment.
 *  @author <TT>AutoDoc</TT>
 */
public class CopyAssignment extends Assignment {


    /**
     * Constructor for the transformation of COMPOST ASTs to KeY.
     * @param children the children of this AST element as KeY classes.
     */
    public CopyAssignment(ExtList children) {
	super(children);
    }

    /**
     * Constructor for the transformation of COMPOST ASTs to KeY.
     * @param lhs the Expression the value is assigned to
     * @param rhs the Expression the value which is assigned to <tt>lhs</tt>
     */
    public CopyAssignment(Expression lhs, Expression rhs) {
	super(lhs, rhs);
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
	v.performActionOnCopyAssignment(this);
    }

    public void prettyPrint(PrettyPrinter p) throws java.io.IOException {
        p.printCopyAssignment(this);
    }
}