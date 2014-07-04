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

import de.uka.ilkd.key.java.PrettyPrinter;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.TypeConverter;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.PrimitiveType;
import de.uka.ilkd.key.java.expression.Operator;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.util.ExtList;

/** The most weird ternary C operator ?: */

public class Conditional extends Operator {


    /**
     *      Conditional.
     *      @param children list of children the first one is the guard expression, 
     *      the second one the then expression and the last one the else expr.
     */

    public Conditional(ExtList children) {
	super(children);
    }


    /**
 *      Get arity.
 *      @return the int value.
     */

    public int getArity() {
        return 3;
    }

    /**
 *      Get precedence.
 *      @return the int value.
     */

    public int getPrecedence() {
        return 12;
    }

    /**
 *      Get notation.
 *      @return the int value.
     */

    public int getNotation() {
        return INFIX;
    }

    /**
 *        Checks if this operator is left or right associative. Conditionals
 *        are right associative.
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
	v.performActionOnConditional(this);
    }

    public void prettyPrint(PrettyPrinter p) throws java.io.IOException {
        p.printConditional(this);
    }

    public KeYJavaType getKeYJavaType(Services javaServ, ExecutionContext ec) {
	final TypeConverter tc = javaServ.getTypeConverter();
	final KeYJavaType type1 = tc.getKeYJavaType(getExpressionAt(1), ec);
	final KeYJavaType type2 = tc.getKeYJavaType(getExpressionAt(2), ec);
	if (tc.isIdentical(type1, type2))
	    return type1;

	// numeric types
	if (tc.isNumericalType(type1) &&
	    tc.isNumericalType(type2) ) {
	    if (type1.getJavaType() == PrimitiveType.JAVA_BYTE &&
		type2.getJavaType() == PrimitiveType.JAVA_SHORT || 
		type1.getJavaType() == PrimitiveType.JAVA_SHORT &&
		type2.getJavaType() == PrimitiveType.JAVA_BYTE)
		return javaServ.getJavaInfo().
		    getKeYJavaType(PrimitiveType.JAVA_SHORT);
	    if (tc.isImplicitNarrowing(getExpressionAt(1),
						  (PrimitiveType)type2.getJavaType()))
		return type2;
	    if (tc.isImplicitNarrowing(getExpressionAt(2),
						  (PrimitiveType)type1.getJavaType()))
		return type1;
	    return tc.getPromotedType(type1, type2);
	}
	

	// reference types
	if (tc.isNullType(type1) &&
	    tc.isReferenceType(type2))
	    return type2;
	if (tc.isNullType(type2) &&
	    tc.isReferenceType(type1))
	    return type1;
	if (tc.isAssignableTo(type1, type2))
	    return type2;
	if (tc.isAssignableTo(type2, type1))
	    return type1;

	throw new RuntimeException("Could not determine type of conditional "+
				   "expression\n"+this+". This usually means that "+
				   "the Java program is not compilable.");
    }

}