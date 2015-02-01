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

package de.uka.ilkd.key.rule.metaconstruct;

import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.PrimitiveType;
import de.uka.ilkd.key.java.declaration.LocalVariableDeclaration;
import de.uka.ilkd.key.java.declaration.VariableSpecification;
import de.uka.ilkd.key.java.declaration.modifier.Ghost;
import de.uka.ilkd.key.java.expression.ParenthesizedExpression;
import de.uka.ilkd.key.java.expression.literal.EmptySeqLiteral;
import de.uka.ilkd.key.java.expression.operator.*;
import de.uka.ilkd.key.java.expression.operator.adt.SeqConcat;
import de.uka.ilkd.key.java.expression.operator.adt.SeqSingleton;
import de.uka.ilkd.key.java.reference.*;
import de.uka.ilkd.key.java.statement.*;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.speclang.LoopInvariant;
import de.uka.ilkd.key.util.ExtList;

/**
 * 
 * This class defines a meta operator to resolve an enhanced for loop - by
 * transformation to a "normal" loop.
 * 
 * This class is used to transform an enh. for loop over an iterable object into
 * a while loop + surrounding statements.
 * 
 * @author mulbrich, bruns
 * 
 */

public class EnhancedForElimination extends ProgramTransformer {

    private static final String IT = "it";
    private static final String ARR = "arr";
    private static final String VALUES = "values";
    private static final String ITERABLE_CLASS_NAME = "java.lang.Iterable";
    private static final String ITERATOR_METH = "iterator";
    private static final String HAS_NEXT = "hasNext";
    private static final String NEXT = "next";
    private static final String ITERATOR = "java.util.Iterator";

    public EnhancedForElimination(EnhancedFor forStatement) {
        super("enhancedfor-elim", forStatement);
    }

    /**
     * An enhanced for loop is executed by transforming it into a "normal" for
     * loop.
     * 
     * For an enhanced for "for(type var : exp) stm" the fields of LoopStatement
     * are used as follows:
     * <ul>
     * <li>inits: type var
     * <li>guard: exp
     * <li>updates remains empty
     * <li>body: stm
     * </ul>
     * 
     * <p>
     * Loops over arrays are treated by a taclet without use of this class.
     * 
     * <p>
     * Loops over Iterable-objects are treated by this meta-construct.
     * 
     * <p>
     * The rules which use this meta construct must ensure that exp is of type
     * Iterable.
     * 
     * @see #makeIterableForLoop(LocalVariableDeclaration, Expression,
     *      Statement)
     * 
     * @see de.uka.ilkd.key.rule.metaconstruct.ProgramTransformer#transform(de.uka.ilkd.key.java.ProgramElement,
     *      de.uka.ilkd.key.java.Services,
     *      de.uka.ilkd.key.rule.inst.SVInstantiations)
     */
    @Override
    public ProgramElement transform(ProgramElement pe,
            Services services, SVInstantiations svInst) {

        assert pe instanceof EnhancedFor : "Only works on enhanced fors";

        EnhancedFor enhancedFor = (EnhancedFor) pe;

        Expression expression = enhancedFor.getGuardExpression();

        ProgramElement result;
        if(isIterable(expression, services)) {
            result = makeIterableForLoop(enhancedFor, services);
        } else {
            result = makeArrayForLoop(enhancedFor, services);
        }
        
        return result;
    }

    /**
     * Checks if an expression is an {@code Iterable}.
     *
     * @param expression the expression to check
     * @param services the services for lookups
     * @return true, if expression's type is a subtype of Iterable
     */
    private boolean isIterable(Expression expression, Services services) {
        JavaInfo ji = services.getJavaInfo();
        // TODO: how to get a more appropriate execution context?
        final ExecutionContext ec = ji.getDefaultExecutionContext();
        boolean iterable = ji.isSubtype(expression.getKeYJavaType(services, ec),
                ji.getTypeByName(ITERABLE_CLASS_NAME));
        return iterable;
    }

    /*
     * Transform an enhanced for-loop over an array to a regular for-loop.
     *   for(T v : exp) body
     * -->
     *   arr = exp;
     *   for(int i = 0; i < arr.length; i++) body;
     */
    private ProgramElement makeArrayForLoop(EnhancedFor enhancedFor, Services services) {

        Expression expression = enhancedFor.getGuardExpression();
        Statement body = enhancedFor.getBody();

        assert expression instanceof ReferencePrefix :
            expression + " is not an arrray reference.";

        final JavaInfo ji = services.getJavaInfo();

        // T[] arr = exp;
        // TODO: how to get a more appropriate execution context?
        final ExecutionContext ec = ji.getDefaultExecutionContext();
        final KeYJavaType arrayType = expression.getKeYJavaType(services, ec);
        final ProgramVariable arrayVar = KeYJavaASTFactory.localVariable(services,
                ARR, arrayType);
        final Statement arrAssignment = KeYJavaASTFactory.declare(arrayVar, expression);

        // for(int i; i < arr.length; i++)
        final KeYJavaType intType = ji.getPrimitiveKeYJavaType("int");
        final ProgramVariable itVar = KeYJavaASTFactory.localVariable(services, "i", intType);
	final ILoopInit inits = KeYJavaASTFactory.loopInitZero(intType, itVar);
        final IGuard guard = KeYJavaASTFactory.lessThanArrayLengthGuard(ji, itVar, arrayVar);
        final IForUpdates updates = KeYJavaASTFactory.postIncrementForUpdates(itVar);

        // there may be only one variable iterated over (see Language Specification Sect. 14.14.2)
        final LocalVariableDeclaration lvd = enhancedFor.getVariableDeclaration();
        final IProgramVariable programVariable = lvd.getVariables().get(0).getProgramVariable();
        assert programVariable instanceof ProgramVariable :
            "Since this is a concrete program, the spec must not be schematic";
        final ProgramVariable lvdVar = (ProgramVariable)programVariable;
        final Statement declArrayElemVar = KeYJavaASTFactory.declare(lvdVar);

        // a = arr[i];
        // assign element of the current iteration to the enhanced for-loop iterator variable
        final Statement getNextElement = KeYJavaASTFactory.assignArrayField(lvdVar, arrayVar, itVar);
        final For forLoop = KeYJavaASTFactory.forLoop(inits, guard,
                updates, declArrayElemVar, getNextElement, body);

        setInvariant(enhancedFor, forLoop, services);

        // arr = exp; for(...) body
        StatementBlock composition = KeYJavaASTFactory.block(arrAssignment, forLoop);
        return composition;
    }

    // Methods to transform loops over Iterable

    /*
     * "{ ; while(<itguard>) <block> } "
     */
    private ProgramElement makeIterableForLoop(EnhancedFor enhancedFor, Services services) {

        // local variable "it"
        final KeYJavaType iteratorType = services.getJavaInfo().getTypeByName(ITERATOR);
	final ProgramVariable itVar = KeYJavaASTFactory.localVariable(services,
		IT, iteratorType);

        // local variable "values"
        final KeYJavaType seqType = services.getTypeConverter().getKeYJavaType(PrimitiveType.JAVA_SEQ);
	final ProgramVariable valuesVar = KeYJavaASTFactory.localVariable(
		services, VALUES, seqType);

	// ghost \seq values = \seq_empty
	final Statement valuesInit = KeYJavaASTFactory.declare(new Ghost(),
		valuesVar, EmptySeqLiteral.INSTANCE, seqType);

	// Iterator itVar = expression.iterator();
	final Statement itinit = KeYJavaASTFactory.declareMethodCall(
                iteratorType, itVar, new ParenthesizedExpression(enhancedFor.getGuardExpression()),
		ITERATOR_METH);

	// create the method call itVar.hasNext();
	final Expression itGuard = KeYJavaASTFactory
		.methodCall(itVar, HAS_NEXT);

        final LocalVariableDeclaration lvd = enhancedFor.getVariableDeclaration();
        final StatementBlock block = makeBlock(itVar, valuesVar, lvd, enhancedFor.getBody());

        // while
        final While whileGuard = new While(itGuard, block, null, new ExtList());

        // block
        final StatementBlock outerBlock = KeYJavaASTFactory.block(itinit, valuesInit, whileGuard);
        setInvariant(enhancedFor, whileGuard, services);
        return outerBlock;

    }

    /*
     * "; <body>"
     */
    private StatementBlock makeBlock(ProgramVariable itVar,
	    ProgramVariable valuesVar, LocalVariableDeclaration lvd,
	    Statement body) {
	// create the variable declaration <Type> lvd = itVar.next();
	final VariableSpecification varSpec = lvd.getVariableSpecifications()
		.get(0);
	final LocalVariableDeclaration varDecl = KeYJavaASTFactory
		.declareMethodCall(varSpec.getProgramVariable(), itVar, NEXT);

	// ATTENTION: in order for the invariant rule to work correctly,
	// the update to values needs to appear at the _second_ entry of the
	// loop
	return KeYJavaASTFactory.block(varDecl,
		makeValuesUpdate(valuesVar, lvd), body);
    }

    /*
     * <values> = \seq_concat(<values>, \seq_singleton(<lvd>)); 
     */
    private Statement makeValuesUpdate(ProgramVariable valuesVar, LocalVariableDeclaration lvd){
        final VariableSpecification var = lvd.getVariables().get(0);
        final IProgramVariable element = var.getProgramVariable();
        assert element instanceof ProgramVariable :
            "Since this is a concrete program, the spec must not be schematic";
        final Expression seqSingleton = new SeqSingleton((ProgramVariable)element);
        final Expression seqConcat = new SeqConcat(valuesVar, seqSingleton);
        final Statement assignment = new CopyAssignment(valuesVar, seqConcat);
        return assignment;
    }

    /**
     * Transfer the invariant from <code>original</code> enhanced loop to the
     * <code>transformed</code> while or for loop.
     * @param services
     */
    private void setInvariant (EnhancedFor original, LoopStatement transformed, Services services) {
        LoopInvariant li = services.getSpecificationRepository().getLoopInvariant(original);
        if (li != null) {
            li = li.setLoop(transformed);
            services.getSpecificationRepository().addLoopInvariant(li);
        }
    }
}