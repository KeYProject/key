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
import de.uka.ilkd.key.java.reference.ReferencePrefix;
import de.uka.ilkd.key.java.statement.*;
import de.uka.ilkd.key.logic.GenericTermReplacer;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramSV;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.sort.ArraySort;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.speclang.LoopSpecification;

import org.key_project.util.ExtList;
import org.key_project.util.collection.ImmutableSLList;
import org.key_project.util.collection.Pair;

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
     */
    private static final String IT = "it";

    /**
     * Name for the array variable.
     */
    private static final String ARR = "arr";

    /**
     * Name for the {@code \index} variable.
     */
    private static final String INDEX = "idx";

    /**
     * Name for the {@code \values} variable.
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
     * Execution context sv.
     */
    private final ProgramSV execContextSV;


    /**
     * Creates a new enhanced for-loop elimination.
     *
     * @param execContextSV the execution context.
     * @param forStatement the enhanced for loop to eliminate.
     */
    public EnhancedForElimination(ProgramSV execContextSV, EnhancedFor forStatement) {
        super("enhancedfor-elim", forStatement);
        this.execContextSV = execContextSV;
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
     * @see #makeIterableForLoop(EnhancedFor, TransformationData, Services)
     *
     * @see ProgramTransformer#transform(ProgramElement, Services,
     *      SVInstantiations)
     */
    @Override
    public ProgramElement[] transform(ProgramElement pe, Services services,
            SVInstantiations svInst) {
        final ProgramElement result =
            doTransform(pe, services, svInst).getResult();
        return new ProgramElement[] { result };
    }

    public TransformationData doTransform(ProgramElement pe, Services services,
            SVInstantiations svInst) {
        assert pe instanceof EnhancedFor : "Only works on enhanced fors";

        final EnhancedFor enhancedFor = (EnhancedFor) pe;

        Expression expression = enhancedFor.getGuardExpression();

        final ExecutionContext execContext;
        if (execContextSV == null) {
            execContext = svInst.getContextInstantiation().activeStatementContext();
        } else {
            execContext = (ExecutionContext) svInst.getInstantiation(execContextSV);
        }

        TransformationData data = new TransformationData(execContext);

        ProgramElement result;
        if (!isArrayType(expression, data.execContext, services)) {
            result = makeIterableForLoop(enhancedFor, data, services);
        } else {
            result = makeArrayForLoop(enhancedFor, data, services);
        }
        data.setTransformationResult(result);
        return data;
    }

    /**
     * Checks if an expression has an array type.
     *
     * @param expression the expression to check
     * @param services the services for lookups
     * @return true, if expression's type is a subtype of Iterable
     */
    private boolean isArrayType(Expression expression, ExecutionContext execContext,
            Services services) {
        return expression.getKeYJavaType(services, execContext).getSort() instanceof ArraySort;
    }

    /*
     * Transform an enhanced for-loop over an array to a regular for-loop. for(T v : exp) body -->
     * arr = exp; for(int i = 0; i < arr.length; i++) body;
     */
    private ProgramElement makeArrayForLoop(EnhancedFor enhancedFor, TransformationData data,
            Services services) {
        Expression expression = enhancedFor.getGuardExpression();
        Statement body = enhancedFor.getBody();

        assert expression instanceof ReferencePrefix : expression + " is not an arrray reference.";

        final JavaInfo ji = services.getJavaInfo();

        // T[] arr = exp;
        final KeYJavaType arrayType = expression.getKeYJavaType(services, data.execContext());
        final ProgramVariable arrayVar = KeYJavaASTFactory.localVariable(services, ARR, arrayType);
        final Statement arrAssignment = KeYJavaASTFactory.declare(arrayVar, expression);

        data.setHead(KeYJavaASTFactory.block(arrAssignment));

        // for(int i; i < arr.length; i++)
        final KeYJavaType intType = ji.getPrimitiveKeYJavaType("int");
        data.setIndexVariable(KeYJavaASTFactory.localVariable(services, INDEX, intType));
        final ILoopInit inits = KeYJavaASTFactory.loopInitZero(intType, data.indexVariable());
        final IGuard guard =
            KeYJavaASTFactory.lessThanArrayLengthGuard(ji, data.indexVariable(), arrayVar);
        final IForUpdates updates = KeYJavaASTFactory.postIncrementForUpdates(data.indexVariable());

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
            KeYJavaASTFactory.assignArrayField(lvdVar, arrayVar, data.indexVariable());
        data.setLoop(KeYJavaASTFactory.forLoop(inits, guard, updates, declArrayElemVar,
            getNextElement, body));

        setInvariant(enhancedFor, data.loop(), data.indexVariable(), Optional.empty(), services);

        // arr = exp; for(...) body
        StatementBlock composition = KeYJavaASTFactory.block(arrAssignment, data.loop());
        return composition;
    }

    // Methods to transform loops over Iterable

    /*
     * "{ ; while(<itguard>) <block> } "
     */
    private ProgramElement makeIterableForLoop(EnhancedFor enhancedFor, TransformationData data,
            Services services) {
        final Expression iterableExpr = enhancedFor.getGuardExpression();
        final KeYJavaType iterableType = iterableExpr.getKeYJavaType(services, data.execContext());
        final IProgramMethod iteratorMethod =
            services.getJavaInfo().getProgramMethod(iterableType, ITERATOR_METHOD_NAME,
                ImmutableSLList.nil(), data.execContext().getTypeReference().getKeYJavaType());

        // local variable "it"
        final KeYJavaType iteratorType = iteratorMethod.getReturnType();
        ProgramVariable iteratorVariable =
            KeYJavaASTFactory.localVariable(services, IT, iteratorType);

        // local variable "values"
        final KeYJavaType seqType =
            services.getTypeConverter().getKeYJavaType(PrimitiveType.JAVA_SEQ);
        data.setValuesVariable(KeYJavaASTFactory.localVariable(services, VALUES, seqType));

        // ghost \seq values = \seq_empty
        final Statement valuesInit = KeYJavaASTFactory.declare(new Ghost(), data.valuesVariable(),
            EmptySeqLiteral.INSTANCE, seqType);

        // Iterator itVar = expression.iterator();
        final Statement itinit = KeYJavaASTFactory.declareMethodCall(iteratorType, iteratorVariable,
            new ParenthesizedExpression(enhancedFor.getGuardExpression()), ITERATOR_METHOD_NAME);

        // create the method call itVar.hasNext();
        final Expression itGuard =
            KeYJavaASTFactory.methodCall(iteratorVariable, HAS_NEXT_METHOD_NAME);

        final LocalVariableDeclaration lvd = enhancedFor.getVariableDeclaration();
        final StatementBlock block =
            makeBlock(iteratorVariable, data.valuesVariable(), lvd, enhancedFor.getBody());

        // while
        data.setLoop(new While(itGuard, block, null, new ExtList()));

        data.setHead(KeYJavaASTFactory.block(itinit, valuesInit));

        // block
        final StatementBlock outerBlock = KeYJavaASTFactory.block(itinit, valuesInit, data.loop());
        setInvariant(enhancedFor, data.loop(), data.indexVariable(),
            Optional.of(data.valuesVariable()), services);
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

        Optional<JTerm> maybeVariant = Optional.ofNullable(rawInv.getInternalVariant());
        final Map<LocationVariable, JTerm> newInvs = //
            new LinkedHashMap<>(rawInv.getInternalInvariants());
        final Map<LocationVariable, JTerm> newFreeInvs = //
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
    private void updateInvs(final Map<LocationVariable, JTerm> invs, final JTerm termToReplace,
            final ProgramVariable replaceWith, final Services services) {
        final TermBuilder tb = services.getTermBuilder();
        invs.entrySet().stream().filter(entry -> entry.getValue() != null)
                .map(entry -> new Pair<>(entry.getKey(),
                    GenericTermReplacer.replace(entry.getValue(), termToReplace::equals,
                        t -> tb.var(replaceWith), services)))
                .forEach(p -> invs.put(p.first, p.second));
    }

    public class TransformationData {

        private ProgramVariable indexVariable;
        private ProgramVariable valuesVariable;
        private StatementBlock head;
        private LoopStatement loop;
        private final ExecutionContext execContext;
        private ProgramElement transformationResult;

        public TransformationData(ExecutionContext execContext) {
            this.execContext = execContext;
        }

        public ProgramVariable indexVariable() {
            return indexVariable;
        }

        public ProgramVariable valuesVariable() {
            return valuesVariable;
        }

        public StatementBlock head() {
            return head;
        }

        public LoopStatement loop() {
            return loop;
        }

        public ExecutionContext execContext() {
            return execContext;
        }

        public void setHead(StatementBlock head) {
            this.head = head;
        }

        public void setIndexVariable(ProgramVariable index) {
            this.indexVariable = index;
        }

        public void setValuesVariable(ProgramVariable values) {
            this.valuesVariable = values;
        }

        public void setLoop(LoopStatement loop) {
            this.loop = loop;
        }

        public void setTransformationResult(ProgramElement result) {
            this.transformationResult = result;
        }

        public ProgramElement getResult() {
            return transformationResult;
        }
    }
}
