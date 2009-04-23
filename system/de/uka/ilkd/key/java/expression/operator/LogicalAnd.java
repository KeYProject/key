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
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.expression.Operator;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.util.ExtList;

/**
 *  Logical and.
 */

public class LogicalAnd extends Operator {


    /**
     *      Logical and.
     *      @param children an ExtList with all children of this node
     *      the first children in list will be the one on the left
     *      side, the second the one on the  right side.
     */

    public LogicalAnd(ExtList children) {
        super(children);
    }

    public LogicalAnd(Expression lhs, Expression rhs) {
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
        return 10;
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
	v.performActionOnLogicalAnd(this);
    }

    public void prettyPrint(PrettyPrinter p) throws java.io.IOException {
        p.printLogicalAnd(this);
    }

    public KeYJavaType getKeYJavaType(Services services, ExecutionContext ec) {
	return services.getTypeConverter().getBooleanType();
    }

}
