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
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.util.ExtList;

/**
 *  Equals.
 */

public class Equals extends ComparativeOperator {

    /**
     *      Equals.
     *      @param children an ExtList with all children of this node
     *      the first children in list will be the one on the left
     *      side, the second the one on the  right side.
     */
    public Equals(ExtList children) {
        super(children);
    }

    /**
     * Creates the equals expression <code>lhs==rhs</code>
     * @param lhs the Expression on the left side of the comparison
     * @param rhs the Expression on the right side of the comparison
     */
    public Equals(Expression lhs, Expression rhs) {
        super (lhs, rhs);
    }
     
    /**
 *      Get precedence.
 *      @return the int value.
     */

    public int getPrecedence() {
        return 6;
    }

    /** calls the corresponding method of a visitor in order to
     * perform some action/transformation on this element
     * @param v the Visitor
     */
    public void visit(Visitor v) {
	v.performActionOnEquals(this);
    }

    public void prettyPrint(PrettyPrinter p) throws java.io.IOException {
        p.printEquals(this);
    }
}