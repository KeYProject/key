// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.rule.metaconstruct;

import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.PrimitiveType;
import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.java.expression.Operator;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.ldt.IntegerLDT;
import de.uka.ilkd.key.logic.op.ExpressionOperator;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.NonRigidFunction;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.sort.PrimitiveSort;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

public class InTypeOperator extends ExpressionOperator {

    private static final Name typeof_name = new Name("\\inType");

    public InTypeOperator(Sort sort, Expression expr) {
	super(typeof_name, sort, expr);
    }
    
    private long getUpperBound(String type) {
	if (type.equals("byte")) 
	    return Byte.MAX_VALUE;
	else if (type.equals("short")) 
	    return Short.MAX_VALUE;
	else if (type.equals("int")) 
	    return Integer.MAX_VALUE;
	else if (type.equals("long")) 
	    return Long.MAX_VALUE;
	else if (type.equals("char")) 
	    return Character.MAX_VALUE;
	return 0;
    }

    private long getLowerBound(String type) {
	if (type.equals("byte")) 
	    return Byte.MIN_VALUE;
	else if (type.equals("short")) 
	    return Short.MIN_VALUE;
	else if (type.equals("int")) 
	    return Integer.MIN_VALUE;
	else if (type.equals("long")) 
	    return Long.MIN_VALUE;
	else if (type.equals("char")) 
	    return Character.MIN_VALUE;
	return 0;
    }

    private Term createConstraintTerm(Expression expr, Type type,
				      ExecutionContext ec,
				      Services services) {
        IntegerLDT aiLDT = services.getTypeConverter().getIntegerLDT();
	Function pred=null;
	if (type == PrimitiveType.JAVA_BYTE) {
	    pred = (Function)aiLDT.functions().lookup(new Name("inByte"));
	} else if (type == PrimitiveType.JAVA_SHORT) {
	    pred = (Function)aiLDT.functions().lookup(new Name("inShort"));
	} else if (type == PrimitiveType.JAVA_INT) {
	    pred = (Function)aiLDT.functions().lookup(new Name("inInt"));
        } else if (type == PrimitiveType.JAVA_LONG) {
	    pred = (Function)aiLDT.functions().lookup(new Name("inLong"));
        } else if (type == PrimitiveType.JAVA_CHAR) {
	    pred = (Function)aiLDT.functions().lookup(new Name("inChar"));
	}
	return TermFactory.DEFAULT.createFunctionTerm
	    (pred, services.getTypeConverter().convertToLogicElement(expr, ec)); 
    }

    private Term createConstraintTerm(Expression expr, 				      
				      ExecutionContext ec,
				      Services services) {       
        Type type = services.getJavaInfo().getPrimitiveKeYJavaType(expr).getJavaType();
	return createConstraintTerm(expr, type, ec, services);
    }


    private Term createConstraintTerm(Operator op, 
				      Expression expr1, 
				      ExecutionContext ec,
				      Services services) {
	Expression expr=null;
	if (op instanceof de.uka.ilkd.key.java.expression.operator.Negative) {
	    expr = new de.uka.ilkd.key.java.expression.operator.Negative(expr1);
	}
	        
        Type type = services.getJavaInfo().getPrimitiveKeYJavaType(expr).getJavaType();
	return createConstraintTerm(expr, type, ec, services);
    }


    private Term createConstraintTerm(Operator op, 
				      Expression expr1, Expression expr2,
				      ExecutionContext ec,
				      Services services) {
	Expression expr=null;
	if (op instanceof de.uka.ilkd.key.java.expression.operator.Times) {
	    expr = new de.uka.ilkd.key.java.expression.operator.Times
		(expr1, expr2);
	} else if (op instanceof de.uka.ilkd.key.java.expression.operator.Divide) {
	    expr = new de.uka.ilkd.key.java.expression.operator.Divide
		(expr1, expr2);
	} else if (op instanceof de.uka.ilkd.key.java.expression.operator.Plus) {
	    expr = new de.uka.ilkd.key.java.expression.operator.Plus
		(expr1, expr2);
	} else if (op instanceof de.uka.ilkd.key.java.expression.operator.Minus) {
	    expr = new de.uka.ilkd.key.java.expression.operator.Minus
		(expr1, expr2);
	} else if (op instanceof de.uka.ilkd.key.java.expression.operator.Modulo) {
	    expr = new de.uka.ilkd.key.java.expression.operator.Modulo
		(expr1, expr2);
	}
	Type type = services.getJavaInfo().getPrimitiveKeYJavaType(expr).getJavaType();
	return createConstraintTerm(expr, type, ec, services);
    }
    


    public Term resolveExpression
	(SVInstantiations svInst, Services services) {

	// get expression instantiations
	Expression exp = expression();
	ExecutionContext ec 
	    = (svInst.getContextInstantiation()==null) ? null : 
	    svInst.getContextInstantiation().activeStatementContext();	    
	
	if (exp instanceof de.uka.ilkd.key.java.expression.Operator) {
	    de.uka.ilkd.key.java.expression.Operator op = 
		(de.uka.ilkd.key.java.expression.Operator) exp;
	    Expression[] children = new Expression[op.getExpressionCount()];
	    for (int i = 0; i < op.getExpressionCount(); i++) {
		children[i] = op.getExpressionAt(i);
	    }
	    // top level operator of the child was a unary operator
	    // at the moment the only unary op is a unary minus
	    if (op.getExpressionCount() == 1) {
		Expression expr = (Expression)
		    svInst.getInstantiation((SchemaVariable)children[0]);		
		return createConstraintTerm(expr, ec, services);		
	    }
	    else
		// top level operator of the child was a binary operator
		if (op.getExpressionCount() == 2) {
		    Expression expr1 = (Expression)
			svInst.getInstantiation((SchemaVariable)children[0]);		
		    Expression expr2 = (Expression)
			svInst.getInstantiation((SchemaVariable)children[1]);
		    return createConstraintTerm(op, expr1, expr2, ec, services);		
		}
		else {
		    throw new RuntimeException("Method resolveExpression "+
					       "in Class InTypeOperator failed "+
					       "to resolve expression");		   
		}
	} else if (exp instanceof SchemaVariable){	   
		Expression expr = (Expression)svInst.
		    getInstantiation((SchemaVariable)exp);		
	    return createConstraintTerm(expr, ec, services);			    	
	}

	return TermFactory.DEFAULT.createFunctionTerm
	    (new NonRigidFunction(new Name("ERROR"), 
			  new PrimitiveSort(new Name("ERROR")), 
			  new PrimitiveSort[0]));

    }

}
