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

import org.key_project.util.ExtList;

import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.PrettyPrinter;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.expression.Operator;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.visitor.Visitor;

/**
 *  Positive.
 */

public class Positive extends Operator {


    /**
     *      Positive.
     *      @param expr the Expression 
     */
    public Positive(Expression expr) {
        super(expr);
    }

    /**
     *      Positive.
     *      @param children an ExtList with all children of this node
     */
    public Positive(ExtList children) {
        super(children);
    }

    /**
 *      Get arity.
 *      @return the int value.
     */

    public int getArity() {
        return 1;
    }

    /**
 *      Get precedence.
 *      @return the int value.
     */

    public int getPrecedence() {
        return 1;
    }

    /**
 *      Get notation.
 *      @return the int value.
     */

    public int getNotation() {
        return PREFIX;
    }

    /**
 *        Checks if this operator is left or right associative. Ordinary
 *        unary operators are right associative.
 *        @return <CODE>true</CODE>, if the operator is left associative,
 *        <CODE>false</CODE> otherwise.
     */

    public boolean isLeftAssociative() {
        return false;
    }

    /** calls the corresponding method of a visitor in order to
     * perform some action/transformation on this element
     * @param v the Visitor
     */
    public void visit(Visitor v) {
	v.performActionOnPositive(this);
    }

    public void prettyPrint(PrettyPrinter p) throws java.io.IOException {
        p.printPositive(this);
    }

    public KeYJavaType getKeYJavaType(Services services, ExecutionContext ec) {
	return services.getTypeConverter().
	    getPromotedType(getExpressionAt(0).getKeYJavaType(services, ec));
    }

}