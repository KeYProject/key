// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2011 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.rule.metaconstruct;

import java.util.LinkedList;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.abstraction.ArrayType;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.PrimitiveType;
import de.uka.ilkd.key.java.declaration.LocalVariableDeclaration;
import de.uka.ilkd.key.java.expression.ArrayInitializer;
import de.uka.ilkd.key.java.expression.literal.BooleanLiteral;
import de.uka.ilkd.key.java.expression.literal.IntLiteral;
import de.uka.ilkd.key.java.expression.operator.*;
import de.uka.ilkd.key.java.reference.*;
import de.uka.ilkd.key.java.statement.For;
import de.uka.ilkd.key.java.statement.If;
import de.uka.ilkd.key.java.statement.Then;
import de.uka.ilkd.key.java.statement.Throw;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.VariableNamer;
import de.uka.ilkd.key.logic.op.LocationVariable;
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
    private String createArrayName = "<createArray>";

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
	final Then then = new Then
	    (new Throw(new New(new Expression[0],
			       new TypeRef
			       (services.getJavaInfo().getKeYJavaType
				    ("java.lang.NegativeArraySizeException")),
			       null)));

	return new If(cond, then);
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
	    final LessThan negativeDimension = new LessThan(pvars[i],
							    new IntLiteral(0));
	    if (i == 0) {
		checkDimensions = negativeDimension;
	    } else {
		checkDimensions = new LogicalOr(checkDimensions,
						negativeDimension);
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
	bodyStmnts.add
	    (assign(resultVar,
		    new MethodReference
		    (new ImmutableArray<Expression>(dimensions[0]),
		     new ProgramElementName(createArrayName),
		     new TypeRef(arrayType))));

	if (dimensions.length > 1) {
	    Expression[] baseDim = new Expression[dimensions.length-1];
	    System.arraycopy(dimensions, 1, baseDim, 0, dimensions.length-1);
	    final VariableNamer varNamer = services.getVariableNamer();
	    final KeYJavaType intType = services.getJavaInfo()
		.getKeYJavaType(PrimitiveType.JAVA_INT);
	    final ProgramElementName name 
	    	= varNamer.getTemporaryNameProposal("i");
    	    final ProgramVariable var = new LocationVariable(name, intType);
	    final LocalVariableDeclaration forInit =
		KeYJavaASTFactory.declare(var,
					  new IntLiteral(0),
					  intType);

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

	    final For forLoop = 
		new For(new LoopInitializer[]{forInit},
			new LessThan(pv, dimensions[0]),
			new Expression[]{new PostIncrement(pv)},			
			assign(new ArrayReference
			       ((ReferencePrefix)resultVar, new Expression[]{pv}),
			       new NewArray(baseDim, 
				       	    baseTypeRef, 
				       	    baseType, 
				       	    null, 
				       	    dimensions.length - 1)));

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

 	return new StatementBlock(bodyStmnts.toArray
				  (new Statement[bodyStmnts.size()]));
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
	    assert false : "dubious code";
	    final KeYJavaType kjt = 
		array.getKeYJavaType(services, svInst.getExecutionContext());
	    na = new NewArray(new Expression[0],
			      ((ArrayType)kjt.getJavaType()).getBaseType(),
			      kjt, (ArrayInitializer)pe, 0);
	} else {
	    return pe;
	}

	final int arrayLength =
	    na.getArrayInitializer().getArguments().size();

	final Statement[] body = new Statement[2*arrayLength+1];
	final ProgramVariable[] vars = evaluateInitializers ( body, na, services );

	body[arrayLength] = 
	    assign ( array, createArrayCreation ( na ));
	
	createArrayAssignments(arrayLength + 1, body, vars,  array, na);

	return new StatementBlock ( body );
    }
    

}
