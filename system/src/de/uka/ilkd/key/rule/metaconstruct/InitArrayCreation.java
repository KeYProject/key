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

import java.util.LinkedList;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.abstraction.ArrayType;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.PrimitiveType;
import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.java.declaration.LocalVariableDeclaration;
import de.uka.ilkd.key.java.expression.ArrayInitializer;
import de.uka.ilkd.key.java.expression.literal.BooleanLiteral;
import de.uka.ilkd.key.java.expression.operator.*;
import de.uka.ilkd.key.java.reference.*;
import de.uka.ilkd.key.java.statement.For;
import de.uka.ilkd.key.java.statement.If;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.VariableNamer;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

/**
 * Split an array creation expression with explicit array initializer,
 * creating a creation expression with dimension expression and a list
 * of assignments (-> Java language specification, 15.10)
 *
 * This meta construct delivers the creation expression
 */
public class InitArrayCreation extends InitArray {

    private final SchemaVariable newObjectSV;
    private final static String createArrayName = "<createArray>";

    public InitArrayCreation(SchemaVariable newObjectSV,
			     ProgramElement newExpr) {	
	super("init-array-creation", newExpr); 
	this.newObjectSV = newObjectSV;
    }

    
    /** 
     * trying to create an array of negative length causes a 
     * {@link java.lang.NegativeArraySizeException} to be thrown. The if
     * statement implementing this behaviour is created by this method.
     * @param cond the Expression representing the guard checking if the
     * given length is negative or not
     * @param services the Services offering access to the type model
     * @return an if statement throwing a NegativeArraySizeException if
     * cond is evaluated to false
     */
    private If checkNegativeDimension(Expression cond,
				      Services services) {
	final New exception = KeYJavaASTFactory.newOperator(services
		.getJavaInfo().getKeYJavaType(
			"java.lang.NegativeArraySizeException"));

	return KeYJavaASTFactory.ifThen(cond,
		KeYJavaASTFactory.throwClause(exception));
    }


    /**
     * creates statements for
     *   <ol>
     *     <li> evaluation of the dimension expressions, <li>
     *     <li> check if a dimension is non-negative </li>
     *  </ol>
     * and adds them to given list of statements. Further more the new
     * declared program variables initialised with the evaluated
     * dimension expressions are returned
     * @param bodyStmnts the LinkedList of statements where the new
     * statements are inserted
     * @param dimExpr the ArrayOf<Expression> which describe the array's
     * dimensions
     * @param services the Services object
     */
    private ProgramVariable[] evaluateAndCheckDimensionExpressions
	(LinkedList<Statement> bodyStmnts, ImmutableArray<Expression> dimExpr,
	 Services services) {

	Expression checkDimensions = BooleanLiteral.FALSE;
	ProgramVariable[] pvars = new ProgramVariable[dimExpr.size()];
	final VariableNamer varNamer = services.getVariableNamer();
	final KeYJavaType intType = services.getJavaInfo()
		.getKeYJavaType(PrimitiveType.JAVA_INT);

	for (int i = 0; i<pvars.length; i++) {
	    final ProgramElementName name 
	    	= varNamer.getTemporaryNameProposal("dim" + i);
    	    
	    final LocalVariableDeclaration argDecl =
		KeYJavaASTFactory.
		declare(name,
			dimExpr.get(i),
			intType);
	    pvars[i] = (ProgramVariable)argDecl.getVariables().
	    get(0).getProgramVariable();

	    bodyStmnts.add(argDecl);
	    final LessThan negativeDimension = KeYJavaASTFactory
		    .lessThanZeroOperator(pvars[i]);
	    if (i == 0) {
		checkDimensions = negativeDimension;
	    } else {
		checkDimensions = KeYJavaASTFactory.logicalOrOperator(
			checkDimensions, negativeDimension);
	    }
	}

	bodyStmnts.add(checkNegativeDimension(checkDimensions, services));

	return pvars;
    }



    /**
     * creates an array of dimension <code>dimensions.length</code>
     */
    private void createNDimensionalArray(LinkedList<Statement> bodyStmnts,
					 Expression resultVar,
					 KeYJavaType arrayType,
					 ProgramVariable[] dimensions,
					 Services services) {
	assert dimensions.length > 0;
	bodyStmnts.add(KeYJavaASTFactory.assign(resultVar,
		KeYJavaASTFactory.methodCall(arrayType, createArrayName, dimensions[0])));

	if (dimensions.length > 1) {
	    Expression[] baseDim = new Expression[dimensions.length-1];
	    System.arraycopy(dimensions, 1, baseDim, 0, dimensions.length-1);
	    final VariableNamer varNamer = services.getVariableNamer();
	    final KeYJavaType intType = services.getJavaInfo()
		.getKeYJavaType(PrimitiveType.JAVA_INT);
	    final ProgramElementName name 
	    	= varNamer.getTemporaryNameProposal("i");
	    final LocalVariableDeclaration forInit = KeYJavaASTFactory.declare(
		    name, KeYJavaASTFactory.zeroLiteral(), intType);

	    final ProgramVariable pv = (ProgramVariable)forInit.getVariables().
	    get(0).getProgramVariable();

	    TypeReference baseTypeRef =
		((ArrayType)arrayType.getJavaType()).getBaseType();
	    final KeYJavaType baseType = baseTypeRef.getKeYJavaType();
            
            for(int i = 0; i < dimensions.length - 1; i++){
        	ArrayType at = (ArrayType) baseTypeRef.getKeYJavaType()
        	                                      .getJavaType();
                baseTypeRef = at.getBaseType();                  
            }

	    final For forLoop = KeYJavaASTFactory.forLoop(KeYJavaASTFactory
		    .loopInit(forInit), KeYJavaASTFactory.lessThanGuard(pv,
		    dimensions[0]), KeYJavaASTFactory
		    .postIncrementForUpdates(pv), KeYJavaASTFactory.assign(
		    KeYJavaASTFactory.arrayFieldAccess(
			    (ReferencePrefix) resultVar, pv), KeYJavaASTFactory
			    .newArray(baseTypeRef, dimensions.length - 1,
				    baseDim, baseType)));

	    bodyStmnts.add(forLoop);
	}
    }


    /**
     * executes an array creation without initializers involved 
     */
    private ProgramElement arrayCreationWithoutInitializers
	(Expression newObject, NewArray na, Services services) {
	
	final LinkedList<Statement> bodyStmnts = new LinkedList<Statement>();	

	final ProgramVariable[] dimensions = 
	    evaluateAndCheckDimensionExpressions
	    (bodyStmnts, na.getArguments(), services);

 	final KeYJavaType arrayType = na.getKeYJavaType(services);

	createNDimensionalArray(bodyStmnts, newObject, arrayType, 
				dimensions, services);

	return KeYJavaASTFactory.block(bodyStmnts);
    }
    

    public ProgramElement transform(ProgramElement pe, 
					    Services services,
					    SVInstantiations svInst) {


	final Expression array = (Expression) svInst.getInstantiation ( newObjectSV );

	NewArray na = null;

	if ( pe instanceof NewArray ) {
	    na = (NewArray) pe;
	    if (na.getArrayInitializer() == null) {
		return arrayCreationWithoutInitializers(array, na, services);
	    }
	} else if (pe instanceof ArrayInitializer) {
	    final KeYJavaType kjt = 
		array.getKeYJavaType(services, svInst.getExecutionContext());
	    final ArrayInitializer init = (ArrayInitializer)pe;
	    ArrayType arrayType = null;
	    try {
            arrayType = (ArrayType)kjt.getJavaType();
	    } catch (ClassCastException e) {
	        throw new RuntimeException("Array dimension does not match its definition. This is a Java syntax error.",e);
	    }
        final int dimension = arrayType.getDimension();
        final Expression[] size = { }; // XXX don't know what that is for
        Type baseType = arrayType;
        TypeReference baseTypeRef = null;
        while (baseType instanceof ArrayType) {
            baseTypeRef = ((ArrayType)baseType).getBaseType();
            baseType = baseTypeRef.getKeYJavaType();
        }
        // XXX known issue: multi-dimensional array new declarations are displayed improperly
        assert baseTypeRef != null;
	    na = KeYJavaASTFactory.newArray(baseTypeRef, dimension, init, kjt);
	} else {
	    return pe;
	}

	final int arrayLength =
	    na.getArrayInitializer().getArguments().size();

	final Statement[] body = new Statement[2*arrayLength+1];
	final ProgramVariable[] vars = evaluateInitializers ( body, na, services );

	body[arrayLength] = KeYJavaASTFactory.assign(array,
		createArrayCreation(na));
	
	createArrayAssignments(arrayLength + 1, body, vars,
		(ReferencePrefix) array, na);

	return KeYJavaASTFactory.block(body);
    }
    

}
