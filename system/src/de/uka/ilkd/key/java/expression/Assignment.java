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



package de.uka.ilkd.key.java.expression;

import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.expression.literal.BooleanLiteral;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.util.ExtList;


/** 
 *  An assignment is an operator with side-effects.
 */

public abstract class Assignment extends Operator 
    implements ExpressionStatement {

    public Assignment() {

    }

    /**
     * Constructor for the transformation of COMPOST ASTs to KeY.
     * @param children the children of this AST element as KeY classes.
     * In this case the order of the children is IMPORTANT. 
     * 	May contain:
     * 		2 of Expression (the first Expression as left hand
     * 			side, the second as right hand side), 
     * 		Comments
     */
    public Assignment(ExtList children) {
	super(children);
    }


    /**
       Unary Assignment (e.g. +=, ++).
       @param lhs an expression.
    */
    public Assignment(Expression lhs) {
        super(lhs);
    }

    /**
       Assignment.
       @param lhs an expression.
       @param rhs an expression.
    */
    public Assignment(Expression lhs, Expression rhs) {
        super(lhs, rhs);
    }


    /**
     *        Checks if this operator is left or right associative. Assignments
     *        are right associative.
     *        @return <CODE>true</CODE>, if the operator is left associative,
     *        <CODE>false</CODE> otherwise.
     */

    public boolean isLeftAssociative() {
        return false;
    }


    /**
     * retrieves the type of the assignment expression
     * @param javaServ the Services offering access to the Java model
     * @param ec the ExecutionContext in which the expression is evaluated
     * @return the type of the assignment expression
     */
    public KeYJavaType getKeYJavaType(Services javaServ, ExecutionContext ec) {
	return getExpressionAt(0).getKeYJavaType(javaServ, ec);
    }
    

    /** overriden from Operator
     */
    public String reuseSignature(Services services, ExecutionContext ec) {
	String base=super.reuseSignature(services, ec);
	Expression rhs;
	try{
	    rhs = children.get(1);
	} catch(ArrayIndexOutOfBoundsException e) {
	    // no second argument, e.g. PostIncrement
	    return base;
	}
	if (rhs instanceof BooleanLiteral)
	    return base+"["+rhs+"]";
	else 
	    return base;
    }
    
}
