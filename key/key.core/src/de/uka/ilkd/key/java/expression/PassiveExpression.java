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

package de.uka.ilkd.key.java.expression;

import java.io.IOException;

import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.PrettyPrinter;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.util.ExtList;


/** 
 * Marks an active statement as inactive.
 */
public class PassiveExpression extends ParenthesizedExpression {

    /**
     * Constructor for the transformation of COMPOST ASTs to KeY.
     * @param children the children of this AST element as KeY classes.
     * In this case the order of the children is IMPORTANT. 
     * 	May contain:
     * 		several of Expression (should be one, the first is taken 
     *                         as parenthesized expression), 
     * 		Comments
     */
    public PassiveExpression(ExtList children) {
	super(children);
    }

    public PassiveExpression(Expression child) {
	super(child);
    }

    /** calls the corresponding method of a visitor in order to
     * perform some action/transformation on this element
     * @param v the Visitor
     */
    public void visit(Visitor v) {
	v.performActionOnPassiveExpression(this);
    }

    public void prettyPrint(PrettyPrinter w) throws IOException {
        w.printPassiveExpression(this);
    }
}