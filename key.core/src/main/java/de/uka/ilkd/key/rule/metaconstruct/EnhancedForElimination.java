/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.metaconstruct;

import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Optional;

import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.KeYJavaASTFactory;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.Statement;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.PrimitiveType;
import de.uka.ilkd.key.java.declaration.LocalVariableDeclaration;
import de.uka.ilkd.key.java.declaration.VariableSpecification;
import de.uka.ilkd.key.java.declaration.modifier.Ghost;
import de.uka.ilkd.key.java.expression.ParenthesizedExpression;
import de.uka.ilkd.key.java.expression.literal.EmptySeqLiteral;
import de.uka.ilkd.key.java.expression.operator.CopyAssignment;
import de.uka.ilkd.key.java.expression.operator.adt.SeqConcat;
import de.uka.ilkd.key.java.expression.operator.adt.SeqSingleton;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.reference.IExecutionContext;
import de.uka.ilkd.key.java.reference.ReferencePrefix;
import de.uka.ilkd.key.java.statement.EnhancedFor;
import de.uka.ilkd.key.java.statement.IForUpdates;
import de.uka.ilkd.key.java.statement.IGuard;
import de.uka.ilkd.key.java.statement.ILoopInit;
import de.uka.ilkd.key.java.statement.LoopStatement;
import de.uka.ilkd.key.java.statement.While;
import de.uka.ilkd.key.logic.GenericTermReplacer;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramSV;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.sort.ArraySort;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.speclang.LoopSpecification;
import de.uka.ilkd.key.util.Pair;

import org.key_project.util.ExtList;
import org.key_project.util.collection.ImmutableSLList;

/**
 *
 * This class defines a meta operator to resolve an enhanced for loop - by transformation to a
 * "normal" loop.
 *
 * This class is used to transform an enh. for loop over an iterable object into a while loop +
 * surrounding statements.
 *
 * @author mulbrich, bruns
 *
 */

public class EnhancedForElimination extends ProgramTransformer {

    /**
     * Name for the iterator variable.
     *
     * @see #getIteratorVariable()
     */
    private static final String IT = "it";

    /**
     * Name for the array variable.
     */
    private static final String ARR = "arr";

    /**
     * Name for the {@code \index} variable.
     *
     * @see #getIndexVariable()
     */
    private static final String INDEX = "idx";

    /**
     * Name for the {@code \values} variable.
     *
     * @see #getValuesVariable()
     */
    private static final String VALUES = "values";

    /**
     * {@code iterator} method name.
     */
    private static final String ITERATOR_METHOD_NAME = "iterator";

    /**
     * {@code hasNext} method name.
     */
    private static final String HAS_NEXT_METHOD_NAME = "hasNext";

    /**
     * {@code next} method name.
     */
    private static final String NEXT_METHOD_NAME = "next";

    /**
     * @see #getIndexVariable()
     */
    private ProgramVariable indexVariable;

    /**
     * @see #getValuesVariable()
     */
    private ProgramVariable valuesVariable;

    /**
     * @see #getIteratorVariable()
     */
    private ProgramVariable iteratorVariable;

    /**
     * @see #getHead()
     */
    private StatementBlock head;

    /**
     * @see #getLoop()
     */
    private LoopStatement loop;

    /**
     * Execution context sv.
     */
    private IExecutionContext execContextSV;

    /**
     * Execution context.
     */
    private ExecutionContext execContext;

    /**
     * Creates a new enhaced for-loop elimination.
     *
     * @param execContextSV the execution context.
     * @param forStatement the enhanced for loop to eliminate.
     */
    public EnhancedForElimination(ProgramSV execContextSV, EnhancedFor forStatement) {
        super("enhancedfor-elim", forStatement);
        this.execContextSV = execContextSV;
    }

    /**
     * Creates a new enhaced for-loop elimination.
     *
     * @param execContext the execution context.
     * @param forStatement the enhanced for loop to eliminate.
     */
    public EnhancedForElimination(ExecutionContext execContext, EnhancedFor forStatement) {
        super("enhancedfor-elim", forStatement);
        this.execContext = execContext;
    }

    /**
     * An enhanced for loop is executed by transforming it into a "normal" for loop.
     *
     * For an enhanced for "for(type var : exp) stm" the fields of LoopStatement are used as
     * follows:
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
     * The rules which use this meta construct must ensure that exp is of type Iterable.
     *
     * @see #makeIterableForLoop(LocalVariableDeclaration, Expression, Statement)
     *
     * @see ProgramTransformer#transform(de.uka.ilkd.key.java.ProgramElement, Services,
     *      SVInstantiations)
     */
    @Override
    public ProgramElement[] transform(ProgramElement pe, Services services,
            SVInstantiations svInst) {
        assert pe instanceof EnhancedFor : "Only works on enhanced fors";

        EnhancedFor enhancedFor = (EnhancedFor) pe;

        Expression expression = enhancedFor.getGuardExpression();

        if (execContext == null) {
            if (execContextSV == null) {
                execContext = svInst.getContextInstantiation().activeStatementContext();
            } else {
                execContext =
                    (ExecutionContext) svInst.getInstantiation((SchemaVariable) execContextSV);
            }
        }

        ProgramElement result;
        if (!isArrayType(expression, services)) {
            result = makeIterableForLoop(enhancedFor, services);
        } else {
            result = makeArrayForLoop(enhancedFor, services);
        }

        return new ProgramElement[] { result };
    }

    /**
     *
     * @return the index variable that should replace {@code \index}.
     */
    public ProgramVariable getIndexVariable() {
        return indexVariable;
    }

    /**
     *
     * @return the values variable that should replace {@code \values}.
     */
    public ProgramVariable getValuesVariable() {
        return valuesVariable;
    }

    /**
     *
     * @return the iterator variable.
     */
    public ProgramVariable getIteratorVariable() {
        return iteratorVariable;
    }

    /**
     *
     * @return a block containing all statements to be executed before the transformed loop.
     * @see #getLoop()
     */
    public StatementBlock getHead() {
        return head;
    }

    /**
     *
     * @return the transformed loop.
     * @see #getHead()
     */
    public LoopStatement getLoop() {
        return loop;
    }

    /**
     * Checks if an expression has an array type.
     *
     * @param expression the expression to check
     * @param services the services for lookups
     * @return true, if expression's type is a subtype of Iterable
     */
    private boolean isArrayType(Expression expression, Services services) {
        return expression.getKeYJavaType(services, execContext).getSort() instanceof ArraySort;
    }

    /*
     * Transform an enhanced for-loop over an array to a regular for-loop. for(T v : exp) body -->
     * arr = exp; for(int i = 0; i < arr.length; i++) body;
     */
    private ProgramElement makeArrayForLoop(EnhancedFor enhancedFor, Services services) {
        Expression expression = enhancedFor.getGuardExpression();
        Statement body = enhancedFor.getBody();

        assert expression instanceof ReferencePrefix : expression + " is not an arrray reference.";

        final JavaInfo ji = services.getJavaInfo();

        // T[] arr = exp;
        final KeYJavaType arrayType = expression.getKeYJavaType(services, execContext);
        final ProgramVariable arrayVar = KeYJavaASTFactory.localVariable(services, ARR, arrayType);
        final Statement arrAssignment = KeYJavaASTFactory.declare(arrayVar, expression);

        head = KeYJavaASTFactory.block(arrAssignment);

        // for(int i; i < arr.length; i++)
        final KeYJavaType intType = ji.getPrimitiveKeYJavaType("int");
        indexVariable = KeYJavaASTFactory.localVariable(services, INDEX, intType);
        final ILoopInit inits = KeYJavaASTFactory.loopInitZero(intType, indexVariable);
        final IGuard guard =
            KeYJavaASTFactory.lessThanArrayLengthGuard(ji, indexVariable, arrayVar);
        final IForUpdates updates = KeYJavaASTFactory.postIncrementForUpdates(indexVariable);

        // there may be only one variable iterated over (see Language Specification Sect. 14.14.2)
        final LocalVariableDeclaration lvd = enhancedFor.getVariableDeclaration();
        final IProgramVariable programVariable = lvd.getVariables().get(0).getProgramVariable();
        assert programVariable instanceof ProgramVariable
                : "Since this is a concrete program, the spec must not be schematic";
        final ProgramVariable lvdVar = (ProgramVariable) programVariable;
        final Statement declArrayElemVar = KeYJavaASTFactory.declare(lvdVar);

        // a = arr[i];
        // assign element of the current iteration to the enhanced for-loop iterator variable
        final Statement getNextElement =
            KeYJavaASTFactory.assignArrayField(lvdVar, arrayVar, indexVariable);
        loop = KeYJavaASTFactory.forLoop(inits, guard, updates, declArrayElemVar, getNextElement,
            body);

        setInvariant(enhancedFor, loop, indexVariable, Optional.empty(), services);

        // arr = exp; for(...) body
        StatementBlock composition = KeYJavaASTFactory.block(arrAssignment, loop);
        return composition;
    }

    // Methods to transform loops over Iterable

    /*
     * "{ ; while(<itguard>) <block> } "
     */
    private ProgramElement makeIterableForLoop(EnhancedFor enhancedFor, Services services) {
        final Expression iterableExpr = enhancedFor.getGuardExpression();
        final KeYJavaType iterableType = iterableExpr.getKeYJavaType(services, execContext);
        final IProgramMethod iteratorMethod =
            services.getJavaInfo().getProgramMethod(iterableType, ITERATOR_METHOD_NAME,
                ImmutableSLList.nil(), execContext.getTypeReference().getKeYJavaType());

        // local variable "it"
        final KeYJavaType iteratorType = iteratorMethod.getReturnType();
        ProgramVariable iteratorVariable =
            KeYJavaASTFactory.localVariable(services, IT, iteratorType);

        // local variable "values"
        final KeYJavaType seqType =
            services.getTypeConverter().getKeYJavaType(PrimitiveType.JAVA_SEQ);
        valuesVariable = KeYJavaASTFactory.localVariable(services, VALUES, seqType);

        // ghost \seq values = \seq_empty
        final Statement valuesInit = KeYJavaASTFactory.declare(new Ghost(), valuesVariable,
            EmptySeqLiteral.INSTANCE, seqType);

        // Iterator itVar = expression.iterator();
        final Statement itinit = KeYJavaASTFactory.declareMethodCall(iteratorType, iteratorVariable,
            new ParenthesizedExpression(enhancedFor.getGuardExpression()), ITERATOR_METHOD_NAME);

        // create the method call itVar.hasNext();
        final Expression itGuard =
            KeYJavaASTFactory.methodCall(iteratorVariable, HAS_NEXT_METHOD_NAME);

        final LocalVariableDeclaration lvd = enhancedFor.getVariableDeclaration();
        final StatementBlock block =
            makeBlock(iteratorVariable, valuesVariable, lvd, enhancedFor.getBody());

        // while
        loop = new While(itGuard, block, null, new ExtList());

        head = KeYJavaASTFactory.block(itinit, valuesInit);

        // block
        final StatementBlock outerBlock = KeYJavaASTFactory.block(itinit, valuesInit, loop);
        setInvariant(enhancedFor, loop, indexVariable, Optional.of(valuesVariable), services);
        return outerBlock;

    }

    /*
     * "; <body>"
     */
    private StatementBlock makeBlock(ProgramVariable itVar, ProgramVariable valuesVar,
            LocalVariableDeclaration lvd, Statement body) {
        // create the variable declaration <Type> lvd = itVar.next();
        final VariableSpecification varSpec = lvd.getVariableSpecifications().get(0);
        final LocalVariableDeclaration varDecl = KeYJavaASTFactory
                .declareMethodCall(varSpec.getProgramVariable(), itVar, NEXT_METHOD_NAME);

        // ATTENTION: in order for the invariant rule to work correctly,
        // the update to values needs to appear at the _second_ entry of the
        // loop
        return KeYJavaASTFactory.block(varDecl, makeValuesUpdate(valuesVar, lvd), body);
    }

    /*
     * <values> = \seq_concat(<values>, \seq_singleton(<lvd>));
     */
    private Statement makeValuesUpdate(ProgramVariable valuesVar, LocalVariableDeclaration lvd) {
        final VariableSpecification var = lvd.getVariables().get(0);
        final IProgramVariable element = var.getProgramVariable();
        assert element instanceof ProgramVariable
                : "Since this is a concrete program, the spec must not be schematic";
        final Expression seqSingleton = new SeqSingleton((ProgramVariable) element);
        final Expression seqConcat = new SeqConcat(valuesVar, seqSingleton);
        final Statement assignment = new CopyAssignment(valuesVar, seqConcat);
        return assignment;
    }

    /**
     * Transfer the invariant from <code>original</code> enhanced loop to the
     * <code>transformed</code> while or for loop.
     *
     * @param original original loop.
     * @param transformed transformed loop.
     * @param services services.
     */
    private void setInvariant(EnhancedFor original, LoopStatement transformed,
            ProgramVariable loopIdxVar, Optional<ProgramVariable> valuesVar, Services services) {
        LoopSpecification li = services.getSpecificationRepository().getLoopSpec(original);
        if (li != null) {
            li = li.setLoop(transformed);
            li = instantiateIndexValues(li, loopIdxVar, valuesVar, services);
            services.getSpecificationRepository().addLoopInvariant(li);
        }
    }

    /**
     * Replaces the function symbols "index" and "values" by actual program entities. The index
     * function symbol is a placeholder which stems from translating the <code>\index</code> keyword
     * from JML. The values function symbol is a placeholder which stems from translating the
     * <code>\values</code> keyword from JML.
     *
     * @param rawInv The "raw" invariant.
     * @param loopIdxVar The actual program variable for the index placeholder.
     * @param maybeValuesVar Optional actual program variable for the values placeholder.
     * @param services The {@link Services} object.
     *
     * @return The updated {@link LoopSpecification}, or null if the supplied invariant is null.
     */
    private LoopSpecification instantiateIndexValues(LoopSpecification rawInv,
            ProgramVariable loopIdxVar, Optional<ProgramVariable> maybeValuesVar,
            Services services) {
        final TermBuilder tb = services.getTermBuilder();

        if (rawInv == null) {
            return null;
        }

        Optional<Term> maybeVariant = Optional.ofNullable(rawInv.getInternalVariant());
        final Map<LocationVariable, Term> newInvs = //
            new LinkedHashMap<>(rawInv.getInternalInvariants());
        final Map<LocationVariable, Term> newFreeInvs = //
            new LinkedHashMap<>(rawInv.getInternalFreeInvariants());

        // replace index
        updateInvs(newInvs, tb.index(), loopIdxVar, services);
        updateInvs(newFreeInvs, tb.index(), loopIdxVar, services);

        maybeVariant = maybeVariant.map(v -> GenericTermReplacer.replace(v,
            t -> t.equals(tb.index()), t -> tb.var(loopIdxVar), services));

        // replace values
        maybeValuesVar.ifPresent(v -> updateInvs(newInvs, tb.values(), v, services));
        if (maybeValuesVar.isPresent()) {
            maybeVariant = maybeVariant.map(variant -> GenericTermReplacer.replace(variant,
                t -> t.equals(tb.values()), t -> tb.var(maybeValuesVar.get()), services));
        }

        return rawInv.instantiate(newInvs, newFreeInvs, maybeVariant.orElse(null));
    }

    /**
     * Updates the given invariants (map from heap to a single invariant) by replacing in them
     * termToReplace by a term containing replaceWith.
     *
     * @param invs The invariants in which to replace.
     * @param termToReplace The term to replace.
     * @param replaceWith The program variable from which to create the replacement term.
     * @param services The {@link Services} object.
     */
    private void updateInvs(final Map<LocationVariable, Term> invs, final Term termToReplace,
            final ProgramVariable replaceWith, final Services services) {
        final TermBuilder tb = services.getTermBuilder();
        invs.entrySet().stream().filter(entry -> entry.getValue() != null)
                .map(entry -> new Pair<>(entry.getKey(),
                    GenericTermReplacer.replace(entry.getValue(), termToReplace::equals,
                        t -> tb.var(replaceWith), services)))
                .forEach(p -> invs.put(p.first, p.second));
    }
}
