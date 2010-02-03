// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//


package de.uka.ilkd.key.java.reference;

import de.uka.ilkd.key.java.ArrayOfExpression;
import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.PrettyPrinter;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.util.ExtList;


/**
 *  This constructor reference.
 * 
 */

public class ThisConstructorReference extends SpecialConstructorReference {

    /**
     *      This constructor reference.
     */
    public ThisConstructorReference() {
	super();
    }

    /**
     *      This constructor reference.
     *      @param arguments an expression mutable list.
     */

    public ThisConstructorReference(Expression[] arguments) {
        super(arguments);
    }


    /**
     * This constructor reference.
     * @param arguments an expression mutable list.
     */
    public ThisConstructorReference(ArrayOfExpression arguments) {
        super(arguments);
    }

    /**
     * Constructor for the transformation of COMPOST ASTs to KeY.
     * @param children the children of this AST element as KeY classes.
     * May contain: 
     * 	several of Expression (as initializers of the array),
     *  Comments
     * Must contain:
     *  execution context
     */ 
    public ThisConstructorReference(ExtList children) {
	super(children);
    }

    /** calls the corresponding method of a visitor in order to
     * perform some action/transformation on this element
     * @param v the Visitor
     */
    public void visit(Visitor v) {
	v.performActionOnThisConstructorReference(this);
    }

    public void prettyPrint(PrettyPrinter p) throws java.io.IOException {
        p.printThisConstructorReference(this);
    }
}
