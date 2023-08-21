/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.speclang;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.UnaryOperator;

import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.KeYJavaASTFactory;
import de.uka.ilkd.key.java.Label;
import de.uka.ilkd.key.java.PositionInfo;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.Statement;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.LocalVariableDeclaration;
import de.uka.ilkd.key.java.expression.literal.AbstractIntegerLiteral;
import de.uka.ilkd.key.java.expression.literal.EmptySeqLiteral;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.statement.EnhancedFor;
import de.uka.ilkd.key.java.statement.For;
import de.uka.ilkd.key.java.statement.LabeledStatement;
import de.uka.ilkd.key.java.statement.LoopStatement;
import de.uka.ilkd.key.java.statement.While;
import de.uka.ilkd.key.java.visitor.InnerBreakAndContinueReplacer;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.proof.OpReplacer;
import de.uka.ilkd.key.proof.mgt.SpecificationRepository;
import de.uka.ilkd.key.rule.metaconstruct.EnhancedForElimination;
import de.uka.ilkd.key.speclang.jml.pretranslation.Behavior;
import de.uka.ilkd.key.util.InfFlowSpec;

import org.key_project.util.ExtList;
import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSet;
import org.key_project.util.java.MapUtil;

/**
 * Default implementation for {@link LoopContract}.
 *
 * @see LoopContractImpl.Creator
 *
 * @author lanzinger
 */
public final class LoopContractImpl extends AbstractAuxiliaryContractImpl implements LoopContract {

    /**
     * @see LoopContract#isOnBlock()
     */
    private final boolean onBlock;

    /**
     * @see LoopContract#getDecreases()
     */
    private final Term decreases;

    /**
     * @see LoopContract#getHead()
     */
    private final StatementBlock head;

    /**
     * @see LoopContract#getGuard()
     */
    private final Expression guard;

    /**
     * @see LoopContract#getBody()
     */
    private final StatementBlock body;

    /**
     * @see LoopContract#getTail()
     */
    private final StatementBlock tail;

    /**
     * @see LoopContract#getLoop()
     */
    private final LoopStatement loop;

    /**
     * @see LoopContract#getIndexVariable()
     */
    private final ProgramVariable index;

    /**
     * @see LoopContract#getValuesVariable()
     */
    private final ProgramVariable values;

    /**
     * Services.
     */
    private final Services services;

    /**
     * @see LoopContract#getLoopLabels()
     */
    private final List<Label> loopLabels;

    /**
     * @see LoopContract#isInternalOnly()
     */
    private boolean internalOnly;

    /**
     * @see LoopContract#toBlockContract()
     */
    private BlockContract blockContract;

    /**
     * @see LoopContract#replaceEnhancedForVariables(StatementBlock, Services)
     */
    private LoopContractImpl replacedEnhancedForVars;

    /**
     * Construct a loop contract for a block that starts with a loop.
     *
     * @param baseName the base name.
     * @param block the block this contract belongs to.
     * @param labels all labels belonging to the block.
     * @param method the method containing the block.
     * @param modality this contract's modality.
     * @param preconditions this contract's preconditions on every heap.
     * @param measuredBy this contract's measured-by term.
     * @param postconditions this contract's postconditions on every heap.
     * @param modifiesClauses this contract's modifies clauses on every heap.
     * @param freeModifiesClauses this contract's free modifies clauses on every heap.
     * @param infFlowSpecs this contract's information flow specifications.
     * @param variables this contract's variables.
     * @param transactionApplicable whether or not this contract is applicable for transactions.
     * @param hasMod a map specifying on which heaps this contract has a modified clause.
     * @param hasFreeMod a map specifying on which heaps this contract has a free modified clause.
     * @param decreases the contract's decreases clause.
     * @param functionalContracts the functional contracts corresponding to this contract.
     * @param services services.
     */
    public LoopContractImpl(final String baseName, final StatementBlock block,
            final List<Label> labels, final IProgramMethod method, final Modality modality,
            final Map<LocationVariable, Term> preconditions,
            final Map<LocationVariable, Term> freePreconditions, final Term measuredBy,
            final Map<LocationVariable, Term> postconditions,
            final Map<LocationVariable, Term> freePostconditions,
            final Map<LocationVariable, Term> modifiesClauses,
            final Map<LocationVariable, Term> freeModifiesClauses,
            final ImmutableList<InfFlowSpec> infFlowSpecs, final Variables variables,
            final boolean transactionApplicable, final Map<LocationVariable, Boolean> hasMod,
            final Map<LocationVariable, Boolean> hasFreeMod,
            final Term decreases, ImmutableSet<FunctionalAuxiliaryContract<?>> functionalContracts,
            Services services) {
        super(baseName, block, labels, method, modality,
            preconditions, freePreconditions, measuredBy, postconditions, freePostconditions,
            modifiesClauses, freeModifiesClauses,
            infFlowSpecs, variables, transactionApplicable, hasMod, hasFreeMod,
            functionalContracts);

        onBlock = true;
        this.decreases = decreases;
        this.services = services;

        Set<Label> loopLabels = new HashSet<>();
        Label outerLabel = new ProgramElementName("breakLoop");
        Label innerLabel = new ProgramElementName("continueLoop");
        loopLabels.add(outerLabel);

        SourceElement first = block.getFirstElement();
        while (first instanceof LabeledStatement) {
            LabeledStatement s = (LabeledStatement) first;
            loopLabels.add(s.getLabel());
            first = s.getBody();
        }

        EnhancedForElimination enhancedForElim = null;

        final LoopStatement loop;
        if (first instanceof While || first instanceof For) {
            this.loop = (LoopStatement) first;
            loop = (LoopStatement) first;
        } else if (first instanceof EnhancedFor) {
            this.loop = (LoopStatement) first;

            ExecutionContext ec =
                KeYJavaASTFactory.executionContext(method.getContainerType(), method, null);
            enhancedForElim = new EnhancedForElimination(ec, (EnhancedFor) first);
            enhancedForElim.transform((EnhancedFor) first, services, null);
            loop = enhancedForElim.getLoop();
        } else {
            throw new IllegalArgumentException("Only blocks that begin with a while or a for "
                + "loop may have a loop contract! \n" + "This block begins with "
                + block.getFirstElement());
        }

        if (enhancedForElim == null) {
            index = null;
            values = null;
        } else {
            index = enhancedForElim.getIndexVariable();
            values = enhancedForElim.getValuesVariable();
        }

        this.loopLabels = new ArrayList<>(loopLabels);
        head = getHeadStatement(loop, block, enhancedForElim);
        guard = loop.getGuardExpression();
        body = getBodyStatement(loop, block, outerLabel, innerLabel, this.loopLabels, services);
        tail = getTailStatement(loop, block);

        internalOnly = loop instanceof EnhancedFor || loop instanceof For;
    }

    /**
     * Construct a loop contract for a loop.
     *
     * @param baseName the base name.
     * @param loop the loop this contract belongs to.
     * @param labels all labels belonging to the block.
     * @param method the method containing the block.
     * @param modality this contract's modality.
     * @param preconditions this contract's preconditions on every heap.
     * @param measuredBy this contract's measured-by term.
     * @param postconditions this contract's postconditions on every heap.
     * @param modifiesClauses this contract's modifies clauses on every heap.
     * @param freeModifiesClauses this contract's free modifies clauses on every heap.
     * @param infFlowSpecs this contract's information flow specifications.
     * @param variables this contract's variables.
     * @param transactionApplicable whether or not this contract is applicable for transactions.
     * @param hasMod a map specifying on which heaps this contract has a modified clause.
     * @param hasFreeMod a map specifying on which heaps this contract has a free modified clause.
     * @param decreases the contract's decreases clause.
     * @param functionalContracts the functional contracts corresponding to this contract.
     * @param services services.
     */
    public LoopContractImpl(final String baseName, final LoopStatement loop,
            final List<Label> labels, final IProgramMethod method, final Modality modality,
            final Map<LocationVariable, Term> preconditions,
            final Map<LocationVariable, Term> freePreconditions, final Term measuredBy,
            final Map<LocationVariable, Term> postconditions,
            final Map<LocationVariable, Term> freePostconditions,
            final Map<LocationVariable, Term> modifiesClauses,
            final Map<LocationVariable, Term> freeModifiesClauses,
            final ImmutableList<InfFlowSpec> infFlowSpecs, final Variables variables,
            final boolean transactionApplicable,
            final Map<LocationVariable, Boolean> hasMod,
            final Map<LocationVariable, Boolean> hasFreeMod,
            final Term decreases, ImmutableSet<FunctionalAuxiliaryContract<?>> functionalContracts,
            Services services) {
        super(baseName, new StatementBlock(loop), labels, method, modality,
            preconditions, freePreconditions, measuredBy, postconditions, freePostconditions,
            modifiesClauses, freeModifiesClauses,
            infFlowSpecs, variables, transactionApplicable, hasMod, hasFreeMod,
            functionalContracts);

        onBlock = false;
        this.decreases = decreases;
        this.services = services;
        this.loop = loop;

        Set<Label> loopLabels = new HashSet<>();
        Label outerLabel = new ProgramElementName("breakLoop");
        Label innerLabel = new ProgramElementName("continueLoop");
        loopLabels.add(outerLabel);

        EnhancedForElimination enhancedForElim = null;
        LoopStatement nonEnhancedLoop = loop;
        if (loop instanceof EnhancedFor) {
            ExecutionContext ec =
                KeYJavaASTFactory.executionContext(method.getContainerType(), method, null);
            enhancedForElim = new EnhancedForElimination(ec, (EnhancedFor) loop);
            enhancedForElim.transform(loop, services, null);
            nonEnhancedLoop = enhancedForElim.getLoop();
        }

        if (enhancedForElim == null) {
            index = null;
            values = null;
        } else {
            index = enhancedForElim.getIndexVariable();
            values = enhancedForElim.getValuesVariable();
        }

        this.loopLabels = new ArrayList<>(loopLabels);
        head = getHeadStatement(nonEnhancedLoop, block, enhancedForElim);
        guard = nonEnhancedLoop.getGuardExpression();
        body = getBodyStatement(nonEnhancedLoop, block, outerLabel, innerLabel, this.loopLabels,
            services);
        tail = new StatementBlock();

        internalOnly = loop instanceof EnhancedFor || loop instanceof For;
    }

    /**
     *
     * @param contracts a set of loop contracts to combine.
     * @param services services.
     * @return the combination of the specified loop contracts.
     */
    public static LoopContract combine(ImmutableSet<LoopContract> contracts, Services services) {
        return new Combinator(contracts.toArray(new LoopContract[contracts.size()]), services)
                .combine();
    }

    /**
     * Create replacement map for index and values variables.
     *
     * @param index the index program variable
     * @param values the values program variable
     * @param services the services object
     * @return the new according op replacer
     */
    private static OpReplacer createOpReplacer(final ProgramVariable index,
            final ProgramVariable values, Services services) {
        final Map<SVSubstitute, SVSubstitute> replacementMap = new HashMap<>();
        if (index != null) {
            replacementMap.put(services.getTermBuilder().index(),
                services.getTermBuilder().var(index));
        }
        if (values != null) {
            replacementMap.put(services.getTermBuilder().values(),
                services.getTermBuilder().var(values));
        }
        return new OpReplacer(replacementMap, services.getTermFactory());
    }

    /**
     * Replace the given variable in the given variable map
     *
     * @param vars the old variables
     * @param variable the variable to be replaced
     * @param services the services object
     * @return the new variables
     */
    private static LoopContractImpl replaceVariable(LoopContractImpl vars, ProgramVariable variable,
            Services services) {
        if (variable != null) {
            LocationVariable rem = new LocationVariable(
                services.getVariableNamer().getTemporaryNameProposal(
                    variable.name() + VariablesCreator.REMEMBRANCE_SUFFIX),
                variable.getKeYJavaType());
            vars.variables.remembranceLocalVariables.put((LocationVariable) variable, rem);
        }
        return vars;
    }

    /**
     *
     * @param loop a loop.
     * @param block the block containing the loop.
     * @param enhancedForElim the transformation used to transform the loop, or {@code null}.
     * @return the initializers if the loop is a for-loop, {@code null} otherwise.
     */
    private static StatementBlock getHeadStatement(LoopStatement loop, StatementBlock block,
            EnhancedForElimination enhancedForElim) {
        final StatementBlock sb;

        if (loop instanceof For) {
            ExtList headStatements = new ExtList();

            if (enhancedForElim != null) {
                headStatements.add(enhancedForElim.getHead());
            }

            for (Statement statement : loop.getInitializers()) {
                headStatements.add(statement);
            }

            sb = new StatementBlock(headStatements);
        } else if (loop instanceof While) {
            if (enhancedForElim != null) {
                sb = enhancedForElim.getHead();
            } else {
                sb = null;
            }
        } else {
            throw new IllegalArgumentException("Only blocks that begin with a while or a for "
                + "loop may have a loop contract! \n" + "This block begins with "
                + block.getFirstElement());
        }

        return sb;
    }

    /**
     *
     * @param loop a loop.
     * @param block the block containing the loop.
     * @param outerLabel the label to use for break statements.
     * @param innerLabel the label to use for continue statements.
     * @param loopLabels all labels belonging to the loop.
     * @param services services.
     * @return the loop's body. If the loop is a for-loop, it is transformed to a while-loop.
     * @see InnerBreakAndContinueReplacer
     */
    private static StatementBlock getBodyStatement(LoopStatement loop, StatementBlock block,
            Label outerLabel, Label innerLabel, List<Label> loopLabels, Services services) {
        final StatementBlock sb;

        if (loop instanceof While) {
            if (loop.getBody() instanceof StatementBlock) {
                sb = (StatementBlock) loop.getBody();
            } else {
                sb = new StatementBlock(loop.getBody());
            }
        } else if (loop instanceof For) {
            ExtList bodyStatements = new ExtList();
            bodyStatements.add(loop.getBody());
            StatementBlock innerBody =
                new InnerBreakAndContinueReplacer(new StatementBlock(bodyStatements), loopLabels,
                    outerLabel, innerLabel, services).replace();

            ExtList updateStatements = new ExtList();
            for (Expression statement : loop.getUpdates()) {
                updateStatements.add(statement);
            }

            sb = new StatementBlock(new StatementBlock(
                new LabeledStatement(innerLabel, innerBody, PositionInfo.UNDEFINED),
                new StatementBlock(updateStatements)));
        } else {
            throw new IllegalArgumentException("Only blocks that begin with a while or a for "
                + "loop may have a loop contract! \n" + "This block begins with "
                + block.getFirstElement());
        }

        return sb;
    }

    /**
     *
     * @param loop a loop.
     * @param block the block containing the loop.
     * @return all statements in the block after the loop.
     */
    private static StatementBlock getTailStatement(LoopStatement loop, StatementBlock block) {
        final StatementBlock sb;

        if (loop instanceof For || loop instanceof While) {
            ExtList tailStatements = new ExtList();

            for (int i = 1; i < block.getStatementCount(); ++i) {
                tailStatements.add(block.getStatementAt(i));
            }

            sb = new StatementBlock(tailStatements);
        } else {
            throw new IllegalArgumentException("Only blocks that begin with a while or a for "
                + "loop may have a loop contract! \n" + "This block begins with "
                + block.getFirstElement());
        }

        return sb;
    }

    @Override
    public StatementBlock getHead() {
        return head;
    }

    @Override
    public Expression getGuard() {
        return guard;
    }

    @Override
    public StatementBlock getBody() {
        return body;
    }

    @Override
    public StatementBlock getTail() {
        return tail;
    }

    @Override
    public LoopStatement getLoop() {
        return loop;
    }

    @Override
    public ProgramVariable getIndexVariable() {
        return index;
    }

    @Override
    public ProgramVariable getValuesVariable() {
        return values;
    }

    @Override
    public boolean isOnBlock() {
        return onBlock;
    }

    private enum ReplaceTypes {

        /**
         * Program variable replace type.
         */
        PROGRAM_VARIABLE(ProgramVariable.class),

        /**
         * Abstract integer literal replace type.
         */
        ABSTRACT_INTEGER_LITERAL(AbstractIntegerLiteral.class),

        /**
         * Empty sequence literal replace type.
         */
        EMPTY_SEQ_LITERAL(EmptySeqLiteral.class);

        /**
         * The target class.
         */
        private final Class<?> targetClass;

        ReplaceTypes(Class<?> targetClass) {
            this.targetClass = targetClass;
        }

        public static LoopContractImpl.ReplaceTypes fromClass(Class<?> cls) {
            for (ReplaceTypes c : values()) {
                if (c.targetClass.isAssignableFrom(cls)) {
                    return c;
                }
            }

            throw new AssertionError();
        }
    }

    private static void replaceVariable(ProgramVariable var, ProgramVariable init,
            Map<Term, Term> preReplacementMap, Map<Term, Term> postReplacementMap,
            LoopContractImpl r, Services services) {
        TermBuilder tb = services.getTermBuilder();

        preReplacementMap.put(tb.var(var), tb.var(init));
        postReplacementMap.put(tb.var(r.variables.remembranceLocalVariables.get(var)),
            tb.var(init));
    }

    private static void replaceVariable(ProgramVariable var, AbstractIntegerLiteral init,
            Map<Term, Term> preReplacementMap, Map<Term, Term> postReplacementMap,
            LoopContractImpl r, Services services) {
        TermBuilder tb = services.getTermBuilder();

        preReplacementMap.put(tb.var(var),
            services.getTypeConverter().getIntegerLDT().translateLiteral(init, services));
        postReplacementMap.put(tb.var(r.variables.remembranceLocalVariables.get(var)),
            services.getTypeConverter().getIntegerLDT().translateLiteral(init, services));
    }

    private static void replaceVariable(ProgramVariable var, EmptySeqLiteral init,
            Map<Term, Term> preReplacementMap, Map<Term, Term> postReplacementMap,
            LoopContractImpl r, Services services) {
        TermBuilder tb = services.getTermBuilder();

        preReplacementMap.put(tb.var(var),
            services.getTypeConverter().getSeqLDT().translateLiteral(init, services));
        postReplacementMap.put(tb.var(r.variables.remembranceLocalVariables.get(var)),
            services.getTypeConverter().getSeqLDT().translateLiteral(init, services));
    }

    private static void replaceVariable(ProgramVariable var, Expression init,
            Map<Term, Term> preReplacementMap, Map<Term, Term> postReplacementMap,
            LoopContractImpl r, Services services) {
        switch (ReplaceTypes.fromClass(init.getClass())) {
        case PROGRAM_VARIABLE:
            replaceVariable(var, (ProgramVariable) init, preReplacementMap, postReplacementMap, r,
                services);
            break;
        case ABSTRACT_INTEGER_LITERAL:
            replaceVariable(var, (AbstractIntegerLiteral) init, preReplacementMap,
                postReplacementMap, r, services);
            break;
        case EMPTY_SEQ_LITERAL:
            replaceVariable(var, (EmptySeqLiteral) init, preReplacementMap, postReplacementMap, r,
                services);
            break;
        default:
            throw new AssertionError();
        }
    }

    @Override
    public BlockContract toBlockContract() {
        StatementBlock block = new StatementBlock(new While(getGuard(), getBody()), getTail());
        StatementBlock headAndBlock =
            (head == null) ? new StatementBlock(block) : new StatementBlock(head, block);
        LoopContractImpl r = (LoopContractImpl) replaceEnhancedForVariables(block, services);

        Map<LocationVariable, Term> pre = (head == null) ? r.preconditions : new HashMap<>();
        Map<LocationVariable, Term> freePre =
            (head == null) ? r.freePreconditions : new HashMap<>();
        Map<LocationVariable, Term> post = (head == null) ? r.postconditions : new HashMap<>();
        Map<LocationVariable, Term> freePost =
            (head == null) ? r.freePostconditions : new HashMap<>();
        Map<LocationVariable, Term> modifies = (head == null) ? r.modifiesClauses : new HashMap<>();
        Map<LocationVariable, Term> freeModifies =
            (head == null) ? r.modifiesClauses : new HashMap<>();


        if (head != null) {
            Map<Term, Term> preReplacementMap = new HashMap<>();
            Map<Term, Term> postReplacementMap = new HashMap<>();
            for (int i = 0; i < head.getStatementCount(); ++i) {
                Statement stmt = head.getStatementAt(i);
                if (stmt instanceof LocalVariableDeclaration) {
                    LocalVariableDeclaration decl = (LocalVariableDeclaration) stmt;
                    ProgramVariable var =
                        (ProgramVariable) decl.getVariables().get(0).getProgramVariable();
                    Expression init = decl.getVariables().get(0).getInitializer();
                    replaceVariable(var, init, preReplacementMap, postReplacementMap, r, services);
                }
            }
            OpReplacer preReplacer = new OpReplacer(preReplacementMap, services.getTermFactory());
            OpReplacer postReplacer = new OpReplacer(postReplacementMap, services.getTermFactory());

            for (LocationVariable heap : r.preconditions.keySet()) {
                pre.put(heap, preReplacer.replace(r.preconditions.get(heap)));
            }
            for (LocationVariable heap : r.freePreconditions.keySet()) {
                freePre.put(heap, preReplacer.replace(r.freePreconditions.get(heap)));
            }
            for (LocationVariable heap : r.postconditions.keySet()) {
                post.put(heap, postReplacer.replace(r.postconditions.get(heap)));
            }
            for (LocationVariable heap : r.freePostconditions.keySet()) {
                freePost.put(heap, postReplacer.replace(r.freePostconditions.get(heap)));
            }
            for (LocationVariable heap : r.modifiesClauses.keySet()) {
                modifies.put(heap, preReplacer.replace(r.modifiesClauses.get(heap)));
            }
            for (LocationVariable heap : r.freeModifiesClauses.keySet()) {
                freeModifies.put(heap, preReplacer.replace(r.modifiesClauses.get(heap)));
            }
        }

        if (blockContract == null) {
            blockContract = new BlockContractImpl(
                r.baseName, headAndBlock, r.labels, r.method, r.modality,
                pre, freePre, r.measuredBy, post, freePost, modifies, freeModifies,
                r.infFlowSpecs, r.variables, r.transactionApplicable, r.hasMod, r.hasFreeMod,
                getFunctionalContracts());
            ((BlockContractImpl) blockContract).setLoopContract(this);
        }
        return blockContract;
    }

    @Override
    public void setFunctionalContract(FunctionalAuxiliaryContract<?> contract) {
        super.setFunctionalContract(contract);

        if (internalOnly && !toBlockContract().getFunctionalContracts().contains(contract)) {
            toBlockContract().setFunctionalContract(contract);
        }
    }

    @Override
    public boolean isInternalOnly() {
        return internalOnly;
    }

    @Override
    public List<Label> getLoopLabels() {
        return loopLabels;
    }

    @Override
    public Term getDecreases() {
        return decreases;
    }

    @Override
    public Term getDecreases(Term heap, Term self, Services services) {
        final Map<Term, Term> replacementMap = createReplacementMap(heap,
            new Terms(self, null, null, null, null, null, null, null, null, null), services);
        final OpReplacer replacer =
            new OpReplacer(replacementMap, services.getTermFactory(), services.getProof());
        return replacer.replace(decreases);
    }

    @Override
    public Term getDecreases(Variables variables, Services services) {
        Map<ProgramVariable, ProgramVariable> map = createReplacementMap(variables, services);
        return new OpReplacer(map, services.getTermFactory(), services.getProof())
                .replace(decreases);
    }

    @Override
    public void visit(final Visitor visitor) {
        assert visitor != null;
        visitor.performActionOnLoopContract(this);
    }

    @Override
    public String getName() {
        return "Loop Contract";
    }

    @Override
    public String getUniqueName() {
        if (getTarget() != null) {
            return "Loop Contract " + getBlock().getStartPosition().line() + " "
                + getTarget().getUniqueName();
        } else {
            return "Loop Contract " + getBlock().getStartPosition().line() + " "
                + Math.abs(getBlock().hashCode());
        }
    }

    @Override
    public String getDisplayName() {
        return "Loop Contract";
    }

    @Override
    public LoopContract map(UnaryOperator<Term> op, Services services) {
        Map<LocationVariable, Term> newPreconditions = preconditions.entrySet().stream()
                .collect(MapUtil.collector(Map.Entry::getKey, entry -> op.apply(entry.getValue())));
        Map<LocationVariable, Term> newFreePreconditions = freePreconditions.entrySet().stream()
                .collect(MapUtil.collector(Map.Entry::getKey, entry -> op.apply(entry.getValue())));
        Map<LocationVariable, Term> newPostconditions = postconditions.entrySet().stream()
                .collect(MapUtil.collector(Map.Entry::getKey, entry -> op.apply(entry.getValue())));
        Map<LocationVariable, Term> newFreePostconditions = freePostconditions.entrySet().stream()
                .collect(MapUtil.collector(Map.Entry::getKey, entry -> op.apply(entry.getValue())));
        Map<LocationVariable, Term> newModifiesClauses = modifiesClauses.entrySet().stream()
                .collect(MapUtil.collector(Map.Entry::getKey, entry -> op.apply(entry.getValue())));
        Map<LocationVariable, Term> newFreeModifiesClauses =
            freeModifiesClauses.entrySet().stream().collect(
                MapUtil.collector(Map.Entry::getKey, entry -> op.apply(entry.getValue())));
        Term newMeasuredBy = op.apply(measuredBy);
        Term newDecreases = op.apply(decreases);

        return update(block, newPreconditions, newFreePreconditions, newPostconditions,
            newFreePostconditions, newModifiesClauses, newFreeModifiesClauses,
            infFlowSpecs.stream().map(spec -> spec.map(op)).collect(ImmutableList.collector()),
            variables, newMeasuredBy, newDecreases);
    }

    @Override
    public LoopContract update(final StatementBlock newBlock,
            final Map<LocationVariable, Term> newPreconditions,
            final Map<LocationVariable, Term> newFreePreconditions,
            final Map<LocationVariable, Term> newPostconditions,
            final Map<LocationVariable, Term> newFreePostconditions,
            final Map<LocationVariable, Term> newModifiesClauses,
            final Map<LocationVariable, Term> newFreeModifiesClauses,
            final ImmutableList<InfFlowSpec> newinfFlowSpecs, final Variables newVariables,
            final Term newMeasuredBy, final Term newDecreases) {
        LoopContractImpl result = new LoopContractImpl(baseName, newBlock, labels, method, modality,
            newPreconditions, newFreePreconditions, newMeasuredBy, newPostconditions,
            newFreePostconditions, newModifiesClauses, newFreeModifiesClauses,
            newinfFlowSpecs, newVariables, transactionApplicable, hasMod, hasFreeMod,
            newDecreases, getFunctionalContracts(), services);
        result.internalOnly = internalOnly;
        return result;
    }

    @Override
    public LoopContract update(final LoopStatement newLoop,
            final Map<LocationVariable, Term> newPreconditions,
            final Map<LocationVariable, Term> newFreePreconditions,
            final Map<LocationVariable, Term> newPostconditions,
            final Map<LocationVariable, Term> newFreePostconditions,
            final Map<LocationVariable, Term> newModifiesClauses,
            final Map<LocationVariable, Term> newFreeModifiesClauses,
            final ImmutableList<InfFlowSpec> newinfFlowSpecs, final Variables newVariables,
            final Term newMeasuredBy, final Term newDecreases) {
        LoopContractImpl result = new LoopContractImpl(
            baseName, newLoop, labels, method, modality,
            newPreconditions, newFreePreconditions, newMeasuredBy,
            newPostconditions, newFreePostconditions,
            newModifiesClauses, newFreeModifiesClauses,
            newinfFlowSpecs, newVariables, transactionApplicable, hasMod, hasFreeMod,
            newDecreases, getFunctionalContracts(), services);
        result.internalOnly = internalOnly;
        return result;
    }

    @Override
    public LoopContract replaceEnhancedForVariables(StatementBlock newBlock, Services services) {
        if (replacedEnhancedForVars != null) {
            return replacedEnhancedForVars;
        }

        if (index == null && values == null) {
            replacedEnhancedForVars = (LoopContractImpl) update(newBlock, preconditions,
                freePreconditions, postconditions, freePostconditions, modifiesClauses,
                freeModifiesClauses, infFlowSpecs, variables, measuredBy, decreases);
        } else {
            final OpReplacer replacer = createOpReplacer(index, values, services);

            final Map<LocationVariable, Term> newPreconditions =
                new LinkedHashMap<>();
            final Map<LocationVariable, Term> newFreePreconditions =
                new LinkedHashMap<>();
            final Map<LocationVariable, Term> newPostconditions =
                new LinkedHashMap<>();
            final Map<LocationVariable, Term> newFreePostconditions =
                new LinkedHashMap<>();
            final Map<LocationVariable, Term> newModifiesClauses =
                new LinkedHashMap<>();
            final Map<LocationVariable, Term> newFreeModifiesClauses =
                new LinkedHashMap<LocationVariable, Term>();


            final Term newMeasuredBy = replacer.replace(measuredBy);
            final Term newDecreases = replacer.replace(decreases);

            for (LocationVariable heap : services.getTypeConverter().getHeapLDT().getAllHeaps()) {
                if (heap.name().equals(HeapLDT.SAVED_HEAP_NAME)) {
                    continue;
                }
                newPreconditions.put(heap, replacer.replace(getPrecondition(heap, services)));
                newFreePreconditions.put(heap,
                    replacer.replace(getFreePrecondition(heap, services)));
                newPostconditions.put(heap, replacer.replace(getPostcondition(heap, services)));
                newFreePostconditions.put(heap,
                    replacer.replace(getFreePostcondition(heap, services)));
                newModifiesClauses.put(heap, replacer.replace(getModifiesClause(heap, services)));
                newFreeModifiesClauses.put(heap,
                    replacer.replace(getFreeModifiesClause(heap, services)));
            }
            replacedEnhancedForVars = (LoopContractImpl) update(newBlock, newPreconditions,
                newFreePreconditions, newPostconditions, newFreePostconditions, newModifiesClauses,
                newFreeModifiesClauses, infFlowSpecs, variables, newMeasuredBy, newDecreases);
            replacedEnhancedForVars = replaceVariable(replacedEnhancedForVars, index, services);
            replacedEnhancedForVars = replaceVariable(replacedEnhancedForVars, values, services);
        }

        return replacedEnhancedForVars;
    }

    @Override
    public LoopContract setBlock(StatementBlock newBlock) {
        if (newBlock.equals(block)) {
            return this;
        }

        LoopContractImpl result = new LoopContractImpl(baseName, newBlock, labels, method, modality,
            preconditions, freePreconditions, measuredBy, postconditions, freePostconditions,
            modifiesClauses, freeModifiesClauses, infFlowSpecs, variables, transactionApplicable,
            hasMod, hasFreeMod, decreases, getFunctionalContracts(), services);
        result.internalOnly = internalOnly;
        return result;
    }

    @Override
    public LoopContract setLoop(LoopStatement newLoop) {
        if (newLoop.equals(loop)) {
            return this;
        }

        LoopContractImpl result = new LoopContractImpl(
            baseName, newLoop, labels, method, modality,
            preconditions, freePreconditions, measuredBy, postconditions, freePostconditions,
            modifiesClauses, freeModifiesClauses,
            infFlowSpecs, variables, transactionApplicable, hasMod, hasFreeMod, decreases,
            getFunctionalContracts(), services);
        result.internalOnly = internalOnly;
        return result;
    }

    @Override
    public LoopContract setTarget(KeYJavaType newKJT, IObserverFunction newPM) {
        assert newPM instanceof IProgramMethod;
        assert newKJT.equals(newPM.getContainerType());

        if (newPM.equals(method)) {
            return this;
        }

        LoopContractImpl result = new LoopContractImpl(
            baseName, block, labels, (IProgramMethod) newPM, modality,
            preconditions, freePreconditions, measuredBy, postconditions, freePostconditions,
            modifiesClauses, freeModifiesClauses, infFlowSpecs, variables,
            transactionApplicable, hasMod, hasFreeMod, decreases, getFunctionalContracts(),
            services);
        return result;
    }

    @Override
    public String toString() {
        return "SimpleLoopContract [block=" + block + ", labels=" + labels + ", method=" + method
            + ", modality=" + modality + ", instantiationSelf=" + instantiationSelf
            + ", preconditions=" + preconditions + ", postconditions=" + postconditions
            + ", modifiesClauses=" + modifiesClauses + ", infFlowSpecs=" + infFlowSpecs
            + ", variables=" + variables + ", transactionApplicable=" + transactionApplicable
            + ", hasMod=" + hasMod + "]";
    }

    /**
     * This class is used to build {@link LoopContractImpl}s.
     *
     * @see Creator#create()
     */
    public static class Creator extends AbstractAuxiliaryContractImpl.Creator<LoopContract> {

        /**
         * @see LoopContract#getDecreases()
         */
        private final Term decreases;

        /**
         * {@code null} if this contracts belongs to a block instead of a loop, the loop this
         * contract belongs to otherwise.
         */
        private LoopStatement loop;

        /**
         * Creates loop contract for a block that starts with a loop.
         *
         * @param baseName the contract's base name.
         * @param block the block the contract belongs to.
         * @param labels all labels belonging to the block.
         * @param method the method containing the block.
         * @param behavior the contract's behavior.
         * @param variables the variables.
         * @param requires the contract's precondition.
         * @param measuredBy the contract's measured-by clause.
         * @param ensures the contracts postcondition due to normal termination.
         * @param infFlowSpecs the contract's information flow specifications.
         * @param breaks the contract's postconditions for abrupt termination with {@code break}
         *        statements.
         * @param continues the contract's postconditions for abrupt termination with
         *        {@code continue} statements.
         * @param returns the contract's postcondition for abrupt termination with {@code return}
         *        statements.
         * @param signals the contract's postcondition for abrupt termination due to abrupt
         *        termination.
         * @param signalsOnly a term specifying which uncaught exceptions may occur.
         * @param diverges a diverges clause.
         * @param assignables map from every heap to an assignable term.
         * @param assignablesFree map from every heap to an assignable_free term.
         * @param hasMod map specifying on which heaps this contract has a modifies clause.
         * @param hasFreeMod map specifying on which heaps this contract has a free modifies clause.
         * @param decreases the decreases term.
         * @param services services.
         */
        public Creator(String baseName, StatementBlock block, List<Label> labels,
                IProgramMethod method, Behavior behavior, Variables variables,
                Map<LocationVariable, Term> requires, Map<LocationVariable, Term> requiresFree,
                Term measuredBy, Map<LocationVariable, Term> ensures,
                Map<LocationVariable, Term> ensuresFree, ImmutableList<InfFlowSpec> infFlowSpecs,
                Map<Label, Term> breaks, Map<Label, Term> continues, Term returns, Term signals,
                Term signalsOnly, Term diverges, Map<LocationVariable, Term> assignables,
                Map<LocationVariable, Term> assignablesFree,
                Map<LocationVariable, Boolean> hasMod, Map<LocationVariable, Boolean> hasFreeMod,
                Term decreases, Services services) {
            super(baseName, block, labels, method, behavior, variables,
                requires, requiresFree, measuredBy, ensures, ensuresFree,
                infFlowSpecs, breaks, continues, returns, signals, signalsOnly,
                diverges, assignables, assignablesFree, hasMod, hasFreeMod, services);
            this.decreases = decreases;
        }

        /**
         * Creates loop contract for a loop.
         *
         * @param baseName the contract's base name.
         * @param loop the loop the contract belongs to.
         * @param labels all labels belonging to the block.
         * @param method the method containing the block.
         * @param behavior the contract's behavior.
         * @param variables the variables.
         * @param requires the contract's precondition.
         * @param measuredBy the contract's measured-by clause.
         * @param ensures the contracts postcondition due to normal termination.
         * @param infFlowSpecs the contract's information flow specifications.
         * @param breaks the contract's postconditions for abrupt termination with {@code break}
         *        statements.
         * @param continues the contract's postconditions for abrupt termination with
         *        {@code continue} statements.
         * @param returns the contract's postcondition for abrupt termination with {@code return}
         *        statements.
         * @param signals the contract's postcondition for abrupt termination due to abrupt
         *        termination.
         * @param signalsOnly a term specifying which uncaught exceptions may occur.
         * @param diverges a diverges clause.
         * @param assignables map from every heap to an assignable term.
         * @param assignablesFree map from every heap to an assignable_free term.
         * @param hasMod map specifying on which heaps this contract has a modifies clause.
         * @param hasFreeMod map specifying on which heaps this contract has a free modifies clause.
         * @param decreases the decreases term.
         * @param services services.
         */
        public Creator(String baseName, LoopStatement loop, List<Label> labels,
                IProgramMethod method, Behavior behavior, Variables variables,
                Map<LocationVariable, Term> requires, Map<LocationVariable, Term> requiresFree,
                Term measuredBy, Map<LocationVariable, Term> ensures,
                Map<LocationVariable, Term> ensuresFree, ImmutableList<InfFlowSpec> infFlowSpecs,
                Map<Label, Term> breaks, Map<Label, Term> continues, Term returns, Term signals,
                Term signalsOnly, Term diverges, Map<LocationVariable, Term> assignables,
                Map<LocationVariable, Term> assignablesFree,
                Map<LocationVariable, Boolean> hasMod, Map<LocationVariable, Boolean> hasFreeMod,
                Term decreases, Services services) {
            super(baseName, null, labels, method, behavior, variables,
                requires, requiresFree, measuredBy, ensures, ensuresFree,
                infFlowSpecs, breaks, continues, returns, signals, signalsOnly,
                diverges, assignables, assignablesFree, hasMod, hasFreeMod, services);
            this.loop = loop;
            this.decreases = decreases;
        }

        @Override
        protected LoopContract build(String baseName, StatementBlock block, List<Label> labels,
                IProgramMethod method, Modality modality, Map<LocationVariable, Term> preconditions,
                Map<LocationVariable, Term> freePreconditions, Term measuredBy,
                Map<LocationVariable, Term> postconditions,
                Map<LocationVariable, Term> freePostconditions,
                Map<LocationVariable, Term> modifiesClauses,
                Map<LocationVariable, Term> freeModifiesClauses,
                ImmutableList<InfFlowSpec> infFlowSpecs, Variables variables,
                boolean transactionApplicable, Map<LocationVariable, Boolean> hasMod,
                Map<LocationVariable, Boolean> hasFreeMod) {
            if (block != null) {
                return new LoopContractImpl(
                    baseName, block, labels, method, modality,
                    preconditions, freePreconditions, measuredBy,
                    postconditions, freePostconditions,
                    modifiesClauses, freeModifiesClauses, infFlowSpecs, variables,
                    transactionApplicable, hasMod, hasFreeMod, decreases, null, services);
            } else {
                assert loop != null;
                return new LoopContractImpl(
                    baseName, loop, labels, method, modality,
                    preconditions, freePreconditions,
                    measuredBy, postconditions, freePostconditions,
                    modifiesClauses, freeModifiesClauses, infFlowSpecs, variables,
                    transactionApplicable, hasMod, hasFreeMod, decreases, null, services);
            }
        }

        @Override
        protected Map<LocationVariable, Term> buildPreconditions() {
            final Map<LocationVariable, Term> result = super.buildPreconditions();

            if (decreases != null) {
                result.replaceAll((k, v) -> and(v, geq(decreases, zero())));
            }

            return result;
        }
    }

    /**
     * This class is used to combine multiple contracts for the same block and apply them
     * simultaneously.
     */
    protected static class Combinator
            extends AbstractAuxiliaryContractImpl.Combinator<LoopContract> {

        /**
         *
         * @param contracts the contracts to combine.
         * @param services services.
         */
        public Combinator(LoopContract[] contracts, Services services) {
            super(contracts, services);
        }

        @Override
        protected LoopContract combine() {
            assert contracts.length > 0;
            if (contracts.length == 1) {
                return contracts[0];
            }

            final LoopContract head = contracts[0];
            StringBuilder baseName = new StringBuilder(head.getBaseName());

            for (int i = 1; i < contracts.length; i++) {
                assert contracts[i].getBlock().equals(head.getBlock());

                baseName.append(SpecificationRepository.CONTRACT_COMBINATION_MARKER)
                        .append(contracts[i].getBaseName());
            }

            placeholderVariables = head.getPlaceholderVariables();
            remembranceVariables = placeholderVariables.combineRemembranceVariables();

            ImmutableSet<FunctionalAuxiliaryContract<?>> functionalContracts =
                DefaultImmutableSet.nil();

            for (LoopContract contract : contracts) {
                addConditionsFrom(contract);
                functionalContracts = functionalContracts.union(contract.getFunctionalContracts());
            }

            Map<LocationVariable, Boolean> hasMod = new LinkedHashMap<>();
            Map<LocationVariable, Boolean> hasFreeMod =
                new LinkedHashMap<LocationVariable, Boolean>();
            for (LocationVariable heap : services.getTypeConverter().getHeapLDT().getAllHeaps()) {
                boolean hm = false;
                boolean hfm = false;

                for (int i = 1; i < contracts.length && !hm && !hfm; i++) {
                    hm |= contracts[i].hasModifiesClause(heap);
                    hfm |= contracts[i].hasFreeModifiesClause(heap);
                }
                hasMod.put(heap, hm);
                hasFreeMod.put(heap, hm);
            }

            LoopContractImpl result = new LoopContractImpl(baseName.toString(), head.getBlock(),
                head.getLabels(), head.getMethod(), head.getModality(),
                preconditions, freePreconditions,
                contracts[0].getMby(), postconditions, freePostconditions,
                modifiesClauses, freeModifiesClauses, head.getInfFlowSpecs(),
                placeholderVariables, head.isTransactionApplicable(),
                hasMod, hasFreeMod,
                contracts[0].getDecreases(), functionalContracts, services);

            return result;
        }
    }
}
