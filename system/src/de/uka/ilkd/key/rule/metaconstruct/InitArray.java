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


package de.uka.ilkd.key.rule.metaconstruct;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.abstraction.ArrayType;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.LocalVariableDeclaration;
import de.uka.ilkd.key.java.expression.ArrayInitializer;
import de.uka.ilkd.key.java.expression.operator.NewArray;
import de.uka.ilkd.key.java.reference.ReferencePrefix;
import de.uka.ilkd.key.java.reference.TypeReference;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.util.Debug;

/**
 * Split an array creation expression with explicit array initializer,
 * creating a creation expression with dimension expression and a list
 * of assignments (-> Java language specification, 15.10)
 */
public abstract class InitArray extends ProgramTransformer {

    public InitArray(String name, ProgramElement body) {
	super(name, body);
    }

    /**
     * Extract the variable initializers from the array initializer
     */
    protected ImmutableArray<Expression> extractInitializers(
	    NewArray p_creationExpression) {

	Debug.assertTrue ( p_creationExpression instanceof NewArray,
			   "Don't know how to handle " + p_creationExpression );

	ArrayInitializer aInit = p_creationExpression.getArrayInitializer();

	if ( aInit == null )
	    // nothing to do for us
	    return null;

	return aInit.getArguments ();
    }

    protected KeYJavaType getElementType(NewArray p_creationExpression) {
	Debug.assertTrue ( p_creationExpression instanceof NewArray,
			   "Don't know how to handle " + p_creationExpression );

	KeYJavaType aType = p_creationExpression.getKeYJavaType();

	Debug.assertTrue ( aType.getJavaType () instanceof ArrayType,
			   "Very strange are arrays of type " +
			   aType.getJavaType () );

	return ((ArrayType)aType.getJavaType ()).getBaseType ().getKeYJavaType ();
    }

    /**
     * Create an array creation expression for an array of the size
     * given by the array initializer
     */
    protected Expression createArrayCreation(NewArray p_creationExpression) {

	ImmutableArray<Expression> initializers =
	    extractInitializers ( p_creationExpression );

	if ( initializers == null )
	    return p_creationExpression;

	KeYJavaType arrayType = p_creationExpression.getKeYJavaType();

	return KeYJavaASTFactory.newArray(
		p_creationExpression.getTypeReference(),
		p_creationExpression.getDimensions(),
		KeYJavaASTFactory.intLiteral(initializers.size()), arrayType);
    }


    /**
     * The variable initializers have to be evaluated and assigned to
     * temporary variables (the initializers may itself be array
     * initializers, in which case valid creation expressions are
     * created by inserting the new-operator)
     */
    protected ProgramVariable[] evaluateInitializers 
	( Statement[] p_stmnts, 
	  NewArray p_creationExpression,
	  Services services ) {

	ImmutableArray<Expression> initializers =
	    extractInitializers ( p_creationExpression );

	if ( initializers == null )
	  return new ProgramVariable[0] ;

	KeYJavaType       elementType  =
	    getElementType      ( p_creationExpression );

	int               i   = initializers.size ();
	ProgramVariable[] res = new ProgramVariable [ i ];

	while ( i-- != 0 ) {
	    p_stmnts[i] = KeYJavaASTFactory.declare(services, "_tmpArray",
		    initializers.get(i), elementType);
	    res [i] = (ProgramVariable)
		((LocalVariableDeclaration)p_stmnts[i]).
		getVariables ().get ( 0 ).getProgramVariable ();
	}

	return res;
    }

    /**
     * Convert the variable initializers to assignments to the array
     * elements (the initializers may itself be array initializers, in
     * which case valid creation expressions are created by inserting
     * the new-operator)
     */
    protected void createArrayAssignments (int p_start, 
					   Statement[] p_statements,
					   ProgramVariable[] p_initializers,
					   ReferencePrefix p_array,
					   NewArray p_creationExpression) {

	if ( p_initializers == null ||  
	     p_initializers.length == 0 ) {
	    return ;
	}

	KeYJavaType       elementType  = p_initializers[0].getKeYJavaType ();
	TypeReference baseType = p_creationExpression.getTypeReference();

	int         i   = p_initializers.length;

	while ( i-- != 0 ) {
	    p_statements [p_start + i] = 
		createAssignment ( p_array,
				   i,
				   p_initializers[i],
				   elementType,
				   baseType );
	}
    }

    /**
     * Convert one variable initializers to an assignment to the
     * appropriate array element (the initializer may itself be an
     * array initializer, in which case a valid creation expression is
     * created by inserting the new-operator)
     */
    protected Statement createAssignment ( ReferencePrefix p_array,
					   int            p_index,
					   Expression     p_initializer,
					   KeYJavaType    p_elementType,
					   TypeReference p_baseType) {
	if ( p_initializer instanceof ArrayInitializer ) {
	    Debug.assertTrue ( p_elementType.getJavaType () instanceof ArrayType,
			       "Very strange are arrays of type " +
			       p_elementType.getJavaType () );

	    p_initializer = KeYJavaASTFactory.newArray(p_baseType,
		    ((ArrayType) p_elementType.getJavaType()).getDimension(),
		    (ArrayInitializer) p_initializer, p_elementType);
	}

	Expression indexExpr = KeYJavaASTFactory.intLiteral(p_index);
	Expression lhs = KeYJavaASTFactory.arrayFieldAccess(p_array, indexExpr);

	return KeYJavaASTFactory.assign(lhs, p_initializer);
    }
}
