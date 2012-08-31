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

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.PrimitiveType;
import de.uka.ilkd.key.java.declaration.LocalVariableDeclaration;
import de.uka.ilkd.key.java.declaration.Modifier;
import de.uka.ilkd.key.java.declaration.VariableSpecification;
import de.uka.ilkd.key.java.declaration.modifier.Ghost;
import de.uka.ilkd.key.java.expression.ParenthesizedExpression;
import de.uka.ilkd.key.java.expression.literal.EmptySeqLiteral;
import de.uka.ilkd.key.java.expression.operator.*;
import de.uka.ilkd.key.java.expression.operator.adt.SeqConcat;
import de.uka.ilkd.key.java.expression.operator.adt.SeqSingleton;
import de.uka.ilkd.key.java.reference.*;
import de.uka.ilkd.key.java.statement.*;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.VariableNamer;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.op.LocationVariable;
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
    private static final String VALUES = "values";
    private static final String ITERABLE = "java.lang.Iterable";
    private static final String ITERATOR_METH = "iterator";
    private static final String HAS_NEXT = "hasNext";
    private static final String NEXT = "next";
    private static final String ITERATOR = "java.util.Iterator";
    private Services services;
    private JavaInfo ji;
    private EnhancedFor enhancedFor;

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

        this.services = services;

        enhancedFor = (EnhancedFor) pe;

        LocalVariableDeclaration lvd = enhancedFor.getVariableDeclaration();
        Expression expression = enhancedFor.getGuardExpression();
        Statement body = enhancedFor.getBody();
        

        ProgramElement result;
        if(iterable(expression)) {
            result = makeIterableForLoop(lvd, expression, body);
        } else {
            result = makeArrayForLoop(lvd, expression, body);
        }
        
        return result;
    }

    private boolean iterable(Expression expression) {
        ji = services.getJavaInfo();
        final ExecutionContext ec = ji.getDefaultExecutionContext(); // TODO: how to get a more appropriate one? 
        boolean iterable = ji.isSubtype(expression.getKeYJavaType(services, ec),ji.getTypeByName(ITERABLE));
        return iterable;
    }

    /** Transform an enhanced for-loop over an array to a regular for-loop. */
    private ProgramElement makeArrayForLoop(LocalVariableDeclaration lvd,
            Expression expression, Statement body) {
        assert expression instanceof ReferencePrefix : ""+expression+" is not an arrray reference.";
        // expected subtypes of ReferencePrefix are LocationVariable, VariableReference, etc.
        final ReferencePrefix arrayVar = (ReferencePrefix) expression;
        final VariableNamer varNamer = services.getVariableNamer();
        final ProgramElementName itName = varNamer.getTemporaryNameProposal("i");
        final KeYJavaType intType = ji.getPrimitiveKeYJavaType("int");
        final ProgramVariable itVar = new LocationVariable(itName, intType);

	final ILoopInit inits = KeYJavaASTFactory.loopInit(intType, itVar);
        final IGuard guard = makeGuard(arrayVar, itVar);
        final IForUpdates updates = makeUpdates(itVar);

        // there may be only one variable iterated over (see Language Specification Sect. 14.14.2)
        final IProgramVariable programVariable = lvd.getVariables().get(0).getProgramVariable();
        assert programVariable instanceof ProgramVariable :
            "Since this is a concrete program, the spec must not be schematic";
        final ProgramVariable lvdVar = (ProgramVariable)programVariable;
        final Statement declArrayElemVar = makeElemDecl(lvdVar);

        final For forLoop = makeLoop(body, itVar, inits, guard, updates, arrayVar, lvdVar);

        // put everything together
        final Statement[] complete = {declArrayElemVar,forLoop};
        setInvariant(enhancedFor, forLoop);
        return new StatementBlock(complete);
    }

    /** Declare the iterated element. */
    private Statement makeElemDecl(ProgramVariable lvdVar) {
        final KeYJavaType lvdType = lvdVar.getKeYJavaType();
        final TypeRef lvdTyperef = new TypeRef(lvdType);
        final VariableSpecification lvdSpec = new VariableSpecification(lvdVar, lvdType);
        final Statement declArrayElemVar = new LocalVariableDeclaration(lvdTyperef,lvdSpec);
        return declArrayElemVar;
    }

    /** Loop statement including assignment to the iterated element. */
    private For makeLoop(Statement body, ProgramVariable itVar,
            ILoopInit inits, IGuard guard, IForUpdates updates,
            ReferencePrefix array, ProgramVariable lvdVar) {
        final Expression[] arrayAccess = {itVar};
        final Expression nextElement = new ArrayReference(array, arrayAccess);
        final Statement getNextElement = new CopyAssignment(lvdVar, nextElement);
        final Statement[] newBlock = {getNextElement,body};
        body = new StatementBlock(newBlock);
        final For forLoop = new For(inits, guard, updates, body);
        return forLoop;
    }

    /** Updates to loop index variable (i++). */
    private IForUpdates makeUpdates(ProgramVariable itVar) {
        final Expression[] update = {new PostIncrement(itVar)};
        final IForUpdates updates = new ForUpdates(new ImmutableArray<Expression>(update));
        return updates;
    }

    /** For-loop guard (i < a.length). */
    private IGuard makeGuard(ReferencePrefix expression, ProgramVariable itVar) {
        final ProgramVariable length = ji.getArrayLength();
        final Expression lengthExpr = new FieldReference(length,expression);
        final IGuard guard = new Guard(new LessThan(itVar,lengthExpr));
        return guard;
    }

    // Methods to transform loops over Iterable

    /*
     * "{ ; while(<itguard>) <block> } "
     */
    private ProgramElement makeIterableForLoop(LocalVariableDeclaration lvd,
            Expression expression, Statement body) {

        // local variable "it"
        final VariableNamer varNamer = services.getVariableNamer();
        final KeYJavaType iteratorType = services.getJavaInfo().getTypeByName(ITERATOR);
        final ProgramElementName itName = varNamer.getTemporaryNameProposal(IT);
        final ProgramVariable itVar = new LocationVariable(itName, iteratorType);

        // local variable "values"
        final ProgramElementName valuesName = varNamer.getTemporaryNameProposal(VALUES);
        final KeYJavaType seqType = services.getTypeConverter().getKeYJavaType(PrimitiveType.JAVA_SEQ);
        final LocationVariable valuesVar = new LocationVariable(valuesName, seqType);

        final Statement valuesInit = makeValuesInit(valuesVar);

        final Statement itinit = makeIteratorInit(expression, itVar);

        final Expression itGuard = makeGuard(itVar);

        final StatementBlock block = makeBlock(itVar, valuesVar, lvd, body);

        // while
        final While whileGuard = new While(itGuard, block, null, new ExtList());

        // block
        final Statement[] statements = 
                new Statement[]{ itinit, valuesInit, whileGuard };
        final StatementBlock outerBlock = new StatementBlock(statements);
        setInvariant(enhancedFor,whileGuard);
        return outerBlock;

    }

    /*
     * "ghost \seq values = \seq_empty"
     */
    private Statement makeValuesInit(LocationVariable valuesVar) {
        final KeYJavaType seqType = services.getTypeConverter().getKeYJavaType(PrimitiveType.JAVA_SEQ);
        final TypeReference seqRef = new TypeRef(seqType);
        final Modifier[] ghost = { new Ghost() };
        final Expression seqEmpty = EmptySeqLiteral.INSTANCE;
        final VariableSpecification[] valuesSpec =
            { new VariableSpecification(valuesVar, seqEmpty, seqType) };
        final Statement valuesInit = new LocalVariableDeclaration(ghost, seqRef, valuesSpec);
        return valuesInit;
    }

    /*
     * "; <body>"
     */
    private StatementBlock makeBlock(ProgramVariable itVar, LocationVariable valuesVar,
            LocalVariableDeclaration lvd, Statement body) {

        final Statement[] statements = 
                // ATTENTION: in order for the invariant rule to work correctly,
                // the update to values needs to appear at the _second_ entry of the loop
                { makeUpdate(itVar, lvd), makeValuesUpdate(valuesVar, lvd), body };
        final StatementBlock block = new StatementBlock(statements);
        return block;
    }

    /*
     * <values> = \seq_concat(<values>, \seq_singleton(<lvd>)); 
     */
    private Statement makeValuesUpdate(LocationVariable valuesVar, LocalVariableDeclaration lvd){
        final VariableSpecification var = lvd.getVariables().get(0);
        final IProgramVariable element = var.getProgramVariable();
        assert element instanceof ProgramVariable :
            "Since this is a concrete program, the spec must not be schematic";
        final Expression seqSingleton = new SeqSingleton((ProgramVariable)element);
        final Expression seqConcat = new SeqConcat(valuesVar, seqSingleton);
        final Statement assignment = new CopyAssignment(valuesVar, seqConcat);
        return assignment;
    }

    /*
     * "<Type> <lvd> = <it>.next();"
     */
    private Statement makeUpdate(ProgramVariable itVar,
            LocalVariableDeclaration lvd) {

        final MethodReference methodCall = getItNext(itVar);

        //
        // make local variable decl
        final VariableSpecification orgSpec =
                lvd.getVariableSpecifications().get(0);
        final VariableSpecification newSpec =
                new VariableSpecification(orgSpec.getProgramVariable(),
                        methodCall, orgSpec.getType());
        final KeYJavaType keytype = (KeYJavaType) orgSpec.getType();
        final TypeRef tr = new TypeRef(keytype);
        final LocalVariableDeclaration lvdNew =
                new LocalVariableDeclaration(tr, newSpec);

        return lvdNew;
    }

    /*
     * "<it>.next()"
     */
    private MethodReference getItNext(ProgramVariable itVar) {
        final ProgramElementName nextMeth = new ProgramElementName(NEXT);
        final MethodReference methodCall =
                new MethodReference(new ImmutableArray<Expression>(), nextMeth, itVar);
        return methodCall;
    }

    /*
     * "<it>.hasNext()"
     */
    private Expression makeGuard(ProgramVariable itVar) {
        final ProgramElementName hasNextMeth = new ProgramElementName(HAS_NEXT);
        final MethodReference methodCall =
                new MethodReference(new ImmutableArray<Expression>(), hasNextMeth, itVar);

        return methodCall;
    }

    /*
     * "Iterator <it> = expression.iterator();"
     */
    private Statement makeIteratorInit(Expression expression,
            ProgramVariable itVar) {

        //
        // expression.iterator();
        final MethodName iteratorMeth = new ProgramElementName(ITERATOR_METH);
        final Expression methodcall =
                new MethodReference(new ImmutableArray<Expression>(), iteratorMeth,
                        new ParenthesizedExpression(expression));

        //
        // put together
        final VariableSpecification spec =
                new VariableSpecification(itVar, methodcall, itVar.getKeYJavaType());
        final KeYJavaType iteratorType = services.getJavaInfo().getTypeByName(ITERATOR);
        final TypeRef iteratorTyperef = new TypeRef(iteratorType);
        final LocalVariableDeclaration init =
                new LocalVariableDeclaration(iteratorTyperef, spec);
        return init;
    }

    /**
     * Transfer the invariant from <code>original</code> enhanced loop to the
     * <code>transformed</code> while or for loop.
     */
    private void setInvariant (EnhancedFor original, LoopStatement transformed){
        LoopInvariant li = 
                services.getSpecificationRepository().getLoopInvariant(original);
        if (li != null) {
            li = li.setLoop(transformed);
            services.getSpecificationRepository().setLoopInvariant(li);
        }
    }
}
