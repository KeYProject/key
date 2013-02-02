// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
// 


package de.uka.ilkd.key.java.expression.operator;

import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.PrettyPrinter;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.util.ExtList;


/**
 *  Modulo.
 */
public class Modulo extends BinaryOperator {


    /**
 *      Modulo.
     */

    public Modulo(ExtList children) {
        super(children);
    }

    public Modulo(Expression lhs, Expression rhs) {
	super(lhs, rhs);
    }




    /**
 *      Get precedence.
 *      @return the int value.
     */

    public int getPrecedence() {
        return 2;
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
	v.performActionOnModulo(this);
    }

    public void prettyPrint(PrettyPrinter p) throws java.io.IOException {
        p.printModulo(this);
    }

}
