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

package de.uka.ilkd.key.java.statement;

import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.PrettyPrinter;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.util.ExtList;

/**
 *  Throw.
 */

public class Throw extends ExpressionJumpStatement {

    /**
 *      Throw.
     */

    public Throw() {}

    /**
 *      Throw.
 *      @param expr an expression.
     */

    public Throw(Expression expr) {
        super(expr);
        if (expr == null) {
            throw new IllegalArgumentException("Throw requires one argument");
        }
    }

    /**
 *      Throw.
 *      @param children an ExtList with all children
     */

    public Throw(ExtList children) {
        super(children);
    }

    /** calls the corresponding method of a visitor in order to
     * perform some action/transformation on this element
     * @param v the Visitor
     */
    public void visit(Visitor v) {
	v.performActionOnThrow(this);
    }

    public void prettyPrint(PrettyPrinter p) throws java.io.IOException {
        p.printThrow(this);
    }
}