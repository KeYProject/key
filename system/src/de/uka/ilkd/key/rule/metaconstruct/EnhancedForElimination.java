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
import de.uka.ilkd.key.java.expression.Assignment;
import de.uka.ilkd.key.java.expression.ParenthesizedExpression;
import de.uka.ilkd.key.java.expression.PassiveExpression;
import de.uka.ilkd.key.java.expression.literal.EmptySeqLiteral;
import de.uka.ilkd.key.java.expression.literal.IntLiteral;
import de.uka.ilkd.key.java.expression.operator.*;
import de.uka.ilkd.key.java.reference.*;
import de.uka.ilkd.key.java.statement.*;
import de.uka.ilkd.key.ldt.SeqLDT;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.VariableNamer;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.util.ExtList;

/**
 * 
 * This class defines a meta operator to resolve an enhanced for loop - by
 * transformation to a "normal" loop.
 * 
 * This class is used to transform an enh. for loop over an iterable object into
 * a while loop + surrounding statements.
 * 
 * @author mulbrich
 * 
 */

public class EnhancedForElimination extends ProgramTransformer {

    private static final String ITERABLE = "java.lang.Iterable";
    private static final String ITERATOR_METH = "iterator";
    private static final String HAS_NEXT = "hasNext";
    private static final String NEXT = "next";
    private static final String ITERATOR = "java.util.Iterator";
    private Services services;
    private JavaInfo ji;
    private final boolean ADD_VALUES = true;

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

        EnhancedFor enhancedFor = (EnhancedFor) pe;

        LocalVariableDeclaration lvd = enhancedFor.getVariableDeclaration();
        Expression expression = enhancedFor.getGuardExpression();
        Statement body = enhancedFor.getBody();
        
        ji = services.getJavaInfo();
        ExecutionContext ec = null; // TODO: how to get this? do we need it?
        boolean iterable = ji.isSubtype(expression.getKeYJavaType(services, ec),ji.getTypeByName(ITERABLE));
//        boolean array = ji.isSubtype(expression.getKeYJavaType(services, ec),ji.getTypeByName("java.lang.Object[]"));
//        
//        assert iterable | array : "Enhanced for-loops may only range over arrays or instances of Iterable.";

        ProgramElement result = iterable? makeIterableForLoop(lvd, expression, body) : makeArrayForLoop(lvd, expression, body);
        return result;
    }

    /** Transform an enhanced for-loop over an array to a regular for-loop. */
    private ProgramElement makeArrayForLoop(LocalVariableDeclaration lvd,
            Expression expression, Statement body) {
        VariableNamer varNamer = services.getVariableNamer();
        ProgramElementName itName = varNamer.getTemporaryNameProposal("i");
        KeYJavaType intType = ji.getPrimitiveKeYJavaType("int");
        ProgramVariable itVar = new LocationVariable(itName, intType);
        

        ILoopInit inits = makeForInit(intType, itVar);
        IGuard guard = makeGuard(expression, itVar);
        IForUpdates updates = makeUpdates(itVar);
        
        // there may be only one variable iterated over (see Language Specification Sect. 14.14.2)
        ProgramVariable lvdVar = (ProgramVariable)lvd.getVariables().get(0).getProgramVariable();
        Statement declArrayElemVar = makeElemDecl(lvdVar);
        
        For forLoop = makeLoop(body, itVar, inits, guard, updates, expression,lvdVar);
        
        // put everything together
        Statement[] complete = {declArrayElemVar,forLoop};
        return new StatementBlock(complete);
    }

    /** Declare the iterated element. */
    private Statement makeElemDecl(ProgramVariable lvdVar) {
        KeYJavaType lvdType = lvdVar.getKeYJavaType();
        TypeRef lvdTyperef = new TypeRef(lvdType);
        VariableSpecification lvdSpec = new VariableSpecification(lvdVar, lvdType);
        Statement declArrayElemVar = new LocalVariableDeclaration(lvdTyperef,lvdSpec);
        return declArrayElemVar;
    }

    /** Loop statement including assignment to the iterated element. */
    private For makeLoop(Statement body, ProgramVariable itVar,
            ILoopInit inits, IGuard guard, IForUpdates updates,
            Expression array, ProgramVariable lvdVar) {
        Expression[] arrayAccess = {itVar};
        Expression nextElement = new ArrayReference(new PassiveExpression(array), arrayAccess);
        VariableReference lhs = new VariableReference(lvdVar);
        Statement getNextElement = new CopyAssignment(lhs, nextElement);
        Statement[] newBlock = {getNextElement,body};
        body = new StatementBlock(newBlock);      
        For forLoop = new For(inits, guard, updates, body);
        return forLoop;
    }

    /** Updates to loop index variable (i++). */
    private IForUpdates makeUpdates(ProgramVariable itVar) {
        Expression[] update = {new PostIncrement(itVar)};
        IForUpdates updates = new ForUpdates(new ImmutableArray<Expression>(update));
        return updates;
    }

    /** For-loop guard (i < a.length). */
    private IGuard makeGuard(Expression expression, ProgramVariable itVar) {
        Expression lengthExpr = new ArrayLengthReference(new PassiveExpression(expression));
        IGuard guard = new Guard(new LessThan(itVar,lengthExpr));
        return guard;
    }

    /** Declare index variable and assign zero. */
    private ILoopInit makeForInit(KeYJavaType intType, ProgramVariable itVar) {
        VariableSpecification spec =
                new VariableSpecification(itVar, intType);
        TypeRef intTyperef = new TypeRef(intType);
        LocalVariableDeclaration init =
                new LocalVariableDeclaration(intTyperef, spec);
        Assignment setToZero = new CopyAssignment(itVar, new IntLiteral(0));
        LoopInitializer[] linit = {init,setToZero};
        ILoopInit inits = new LoopInit(linit);
        return inits;
    }
    
    // Methods to transform loops over Iterable

    /*
     * "{ ; while(<itguard>) <block> } "
     */
    private ProgramElement makeIterableForLoop(LocalVariableDeclaration lvd,
            Expression expression, Statement body) {

        VariableNamer varNamer = services.getVariableNamer();
        ProgramElementName itName = varNamer.getTemporaryNameProposal("it");
        ProgramElementName valuesName = varNamer.getTemporaryNameProposal("values");

        Statement valuesInit = makeValuesInit(valuesName);
        
        Statement itinit = makeIteratorInit(expression, itName);

        Expression itGuard = makeGuard(itName);

        StatementBlock block = makeBlock(itName,  valuesName, lvd, body);

        // while
        While whileGuard = new While(itGuard, block, null, new ExtList());

        // block
        Statement[] statements = { itinit, valuesInit, whileGuard };
        StatementBlock outerBlock = new StatementBlock(statements);
        return outerBlock;

    }

    private Statement makeValuesInit(ProgramElementName valuesName) {
        KeYJavaType seqType = services.getTypeConverter().getKeYJavaType(PrimitiveType.JAVA_SEQ);
        TypeReference seqRef = new TypeRef(seqType);
        Modifier[] ghost = {new Ghost()};
        LocationVariable values = new LocationVariable(valuesName, seqType);
        VariableSpecification[] valuesSpec = {new VariableSpecification(values)};
        Statement valuesInit = new LocalVariableDeclaration(ghost,seqRef,valuesSpec);
        Expression seqEmpty = EmptySeqLiteral.INSTANCE;
        Statement setValuesEmpty = new CopyAssignment(values, seqEmpty);
        Statement[] body = ADD_VALUES ? new Statement[]{valuesInit,setValuesEmpty}: new Statement[]{};
        valuesInit = new StatementBlock(body);
        return valuesInit;
    }

    /*
     * "; <body>"
     */
    private StatementBlock makeBlock(ProgramElementName itName, ProgramElementName valuesName,
            LocalVariableDeclaration lvd, Statement body) {

        Statement[] statements = { makeUpdate(itName, valuesName, lvd), body };
        StatementBlock block = new StatementBlock(statements);
        return block;
    }

    /*
     * "<lvd> = <it>.next();"
     */
    private Statement makeUpdate(ProgramElementName itName, ProgramElementName valuesName,
            LocalVariableDeclaration lvd) {

        //
        // it.next()
        KeYJavaType iteratorType =
                services.getJavaInfo().getTypeByName(ITERATOR);
        KeYJavaType seqType = services.getTypeConverter().getKeYJavaType(PrimitiveType.JAVA_SEQ);
        ProgramElementName nextMeth = new ProgramElementName(NEXT);
        ProgramVariable itVar = new LocationVariable(itName, iteratorType);
        ProgramVariable valuesVar = new LocationVariable(valuesName, seqType);
        MethodReference methodCall =
                new MethodReference(new ImmutableArray<Expression>(), nextMeth, itVar);

        //
        // make local variable decl
        VariableSpecification orgSpec =
                lvd.getVariableSpecifications().get(0);
        VariableSpecification newSpec =
                // TODO : use this style elsewhere!
                new VariableSpecification(orgSpec.getProgramVariable(),
                        methodCall, orgSpec.getType());
        KeYJavaType keytype = (KeYJavaType) orgSpec.getType();
        TypeRef tr = new TypeRef(keytype);
        LocalVariableDeclaration lvdNew =
                new LocalVariableDeclaration(tr, newSpec);

        return lvdNew;
    }

    /*
     * "<it>.hasNext()"
     */
    private Expression makeGuard(ProgramElementName itName) {
        KeYJavaType iteratorType =
                services.getJavaInfo().getTypeByName(ITERATOR);
        ProgramElementName hasNextMeth = new ProgramElementName(HAS_NEXT);
        ProgramVariable itVar = new LocationVariable(itName, iteratorType);
        MethodReference methodCall =
                new MethodReference(new ImmutableArray<Expression>(), hasNextMeth, itVar);

        return methodCall;
    }

    /*
     * "Iterator <it> = expression.iterator();"
     */
    private Statement makeIteratorInit(Expression expression,
            ProgramElementName itName) {

        //
        // Iterator it;

        KeYJavaType iteratorType =
                services.getJavaInfo().getTypeByName(ITERATOR);
        ProgramVariable itVar = new LocationVariable(itName, iteratorType);

        //
        // expression.iterator();
        MethodName iteratorMeth = new ProgramElementName(ITERATOR_METH);
        Expression methodcall =
                new MethodReference(new ImmutableArray<Expression>(), iteratorMeth,
                        new ParenthesizedExpression(expression));

        //
        // put together
        VariableSpecification spec =
                new VariableSpecification(itVar, methodcall,
                        itVar.getKeYJavaType());
        TypeRef iteratorTyperef = new TypeRef(iteratorType);
        LocalVariableDeclaration init =
                new LocalVariableDeclaration(iteratorTyperef, spec);
        return init;
    }
}
