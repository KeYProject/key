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
 *  Minus.
 *  @author <TT>AutoDoc</TT>
 */

public class Minus extends BinaryOperator {


    /**
     *      Minus.
     *      @param children an ExtList with all children of this node
     *      the first children in list will be the one on the left
     *      side, the second the one on the  right side.
     */

    public Minus(ExtList children) {
        super(children);
    }

    public Minus(Expression lhs, Expression rhs) {
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
	v.performActionOnMinus(this);
    }

    public void prettyPrint(PrettyPrinter p) throws java.io.IOException {
        p.printMinus(this);
    }



}
