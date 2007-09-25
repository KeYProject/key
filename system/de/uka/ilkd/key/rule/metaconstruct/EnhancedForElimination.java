package de.uka.ilkd.key.rule.metaconstruct;

import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.LocalVariableDeclaration;
import de.uka.ilkd.key.java.declaration.VariableSpecification;
import de.uka.ilkd.key.java.expression.ParenthesizedExpression;
import de.uka.ilkd.key.java.reference.MethodName;
import de.uka.ilkd.key.java.reference.MethodReference;
import de.uka.ilkd.key.java.reference.TypeRef;
import de.uka.ilkd.key.java.statement.EnhancedFor;
import de.uka.ilkd.key.java.statement.While;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.VariableNamer;
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
 * The "array"-case can be handled by a taclet.
 * 
 * @author mulbrich
 * 
 */

public class EnhancedForElimination extends ProgramMetaConstruct {

    private Services services;

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
     * @see de.uka.ilkd.key.rule.metaconstruct.ProgramMetaConstruct#symbolicExecution(de.uka.ilkd.key.java.ProgramElement,
     *      de.uka.ilkd.key.java.Services,
     *      de.uka.ilkd.key.rule.inst.SVInstantiations)
     */
    @Override
    public ProgramElement symbolicExecution(ProgramElement pe,
            Services services, SVInstantiations svInst) {

        assert pe instanceof EnhancedFor : "Only works on enhanced fors";

        this.services = services;

        EnhancedFor enhancedFor = (EnhancedFor) pe;

        LocalVariableDeclaration lvd = enhancedFor.getVariableDeclaration();
        Expression expression = enhancedFor.getGuardExpression();
        Statement body = enhancedFor.getBody();

        return makeIterableForLoop(lvd, expression, body);
    }

    /*
     * "{ <itinit>; while(<itguard>) <block> } "
     */
    private ProgramElement makeIterableForLoop(LocalVariableDeclaration lvd,
            Expression expression, Statement body) {

        VariableNamer varNamer = services.getVariableNamer();
        ProgramElementName itName = varNamer.getTemporaryNameProposal("it");

        Statement itinit = makeIteratorInit(expression, itName);

        Expression itGuard = makeGuard(itName);

        StatementBlock block = makeBlock(itName, lvd, body);

        // while
        While whileGuard = new While(itGuard, block, null, new ExtList());

        // block
        Statement[] statements = { itinit, whileGuard };
        StatementBlock outerBlock = new StatementBlock(statements);
        return outerBlock;

    }

    /*
     * "<update>; <body>"
     */
    private StatementBlock makeBlock(ProgramElementName itName,
            LocalVariableDeclaration lvd, Statement body) {

        Statement[] statements = { makeUpdate(itName, lvd), body };
        StatementBlock block = new StatementBlock(statements);
        return block;
    }

    /*
     * "<lvd> = <it>.next();"
     */
    private Statement makeUpdate(ProgramElementName itName,
            LocalVariableDeclaration lvd) {

        //
        // it.next()
        KeYJavaType iteratorType =
                services.getJavaInfo().getTypeByName("java.util.Iterator");
        ProgramElementName nextMeth = new ProgramElementName("next");
        ProgramVariable itVar = new ProgramVariable(itName, iteratorType);
        MethodReference methodCall =
                new MethodReference(new ArrayOfExpression(), nextMeth, itVar);

        //
        // make local variable decl
        VariableSpecification orgSpec =
                (VariableSpecification) lvd.getVariableSpecifications().getProgramElement(
                        0);
        VariableSpecification newSpec =
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
                services.getJavaInfo().getTypeByName("java.util.Iterator");
        ProgramElementName hasNextMeth = new ProgramElementName("hasNext");
        ProgramVariable itVar = new ProgramVariable(itName, iteratorType);
        MethodReference methodCall =
                new MethodReference(new ArrayOfExpression(), hasNextMeth, itVar);

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
                services.getJavaInfo().getTypeByName("java.util.Iterator");
        ProgramVariable itVar = new ProgramVariable(itName, iteratorType);

        //
        // expression.iterator();
        MethodName iteratorMeth = new ProgramElementName("iterator");
        Expression methodcall =
                new MethodReference(new ArrayOfExpression(), iteratorMeth,
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
