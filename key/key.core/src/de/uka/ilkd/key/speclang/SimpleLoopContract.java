package de.uka.ilkd.key.speclang;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import org.key_project.util.ExtList;
import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSet;

import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.Label;
import de.uka.ilkd.key.java.PositionInfo;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.Statement;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.statement.For;
import de.uka.ilkd.key.java.statement.LabeledStatement;
import de.uka.ilkd.key.java.statement.LoopStatement;
import de.uka.ilkd.key.java.statement.While;
import de.uka.ilkd.key.java.visitor.InnerBreakAndContinueReplacer;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.proof.OpReplacer;
import de.uka.ilkd.key.proof.mgt.SpecificationRepository;
import de.uka.ilkd.key.speclang.jml.pretranslation.Behavior;
import de.uka.ilkd.key.util.InfFlowSpec;

/**
 * Default implementation for {@link LoopContract}.
 *
 * @see SimpleLoopContract.Creator
 *
 * @author lanzinger
 */
public final class SimpleLoopContract extends AbstractBlockSpecificationElement
        implements LoopContract {

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
    private final While loop;

    /**
     * Services.
     */
    private final Services services;

    /**
     * @see LoopContract#getLoopLabels()
     */
    private final List<Label> loopLabels;

    /**
     * @see LoopContract#getFunctionalContracts()
     */
    private ImmutableSet<FunctionalLoopContract> functionalContracts;

    /**
     *
     * @param baseName
     *            the base name.
     * @param block
     *            the block this contract belongs to.
     * @param labels
     *            all labels belonging to the block.
     * @param method
     *            the method containing the block.
     * @param modality
     *            this contract's modality.
     * @param preconditions
     *            this contract's preconditions on every heap.
     * @param measuredBy
     *            this contract's measured-by term.
     * @param postconditions
     *            this contract's postconditions on every heap.
     * @param modifiesClauses
     *            this contract's modifies clauses on every heap.
     * @param infFlowSpecs
     *            this contract's information flow specifications.
     * @param variables
     *            this contract's variables.
     * @param transactionApplicable
     *            whether or not this contract is applicable for transactions.
     * @param hasMod
     *            a map specifying on which heaps this contract has a modified clause.
     * @param decreases
     *            the contract's decreases clause.
     * @param functionalContracts
     *            the functional loop contracts corresponding to this contract.
     * @param services
     *            services.
     */
    public SimpleLoopContract(final String baseName, final StatementBlock block,
            final List<Label> labels, final IProgramMethod method, final Modality modality,
            final Map<LocationVariable, Term> preconditions, final Term measuredBy,
            final Map<LocationVariable, Term> postconditions,
            final Map<LocationVariable, Term> modifiesClauses,
            final ImmutableList<InfFlowSpec> infFlowSpecs, final Variables variables,
            final boolean transactionApplicable, final Map<LocationVariable, Boolean> hasMod,
            final Term decreases, ImmutableSet<FunctionalLoopContract> functionalContracts,
            Services services) {
        super(baseName, block, labels, method, modality, preconditions, measuredBy, postconditions,
                modifiesClauses, infFlowSpecs, variables, transactionApplicable, hasMod);

        this.decreases = decreases;
        this.functionalContracts = functionalContracts;
        this.services = services;

        loopLabels = new ArrayList<Label>();
        Label outerLabel = new ProgramElementName("breakLoop");
        Label innerLabel = new ProgramElementName("continueLoop");
        loopLabels.add(outerLabel);

        SourceElement first = block.getFirstElement();
        while (first instanceof LabeledStatement) {
            LabeledStatement s = (LabeledStatement) first;
            loopLabels.add(s.getLabel());
            first = s.getBody();
        }

        final LoopStatement loop;
        if (first != null && first instanceof While) {
            loop = (While) first;
        } else if (first != null && first instanceof For) {
            loop = (For) first;
        } else {
            loop = null;
            throw new IllegalArgumentException("Only blocks that begin with a while or a for "
                    + "loop may have a loop contract! \n" + "This block begins with "
                    + block.getFirstElement());
        }

        head = getHeadStatement(loop, block);
        guard = loop.getGuardExpression();
        body = getBodyStatement(loop, block, outerLabel, innerLabel, loopLabels, services);
        this.loop = new While(guard, body);
        tail = getTailStatement(loop, block);
    }

    /**
     *
     * @param contracts
     *            a set of loop contracts to combine.
     * @param services
     *            services.
     * @return the combination of the specified loop contracts.
     */
    public static LoopContract combine(ImmutableSet<LoopContract> contracts, Services services) {
        return new Combinator(contracts.toArray(new LoopContract[contracts.size()]), services)
                .combine();
    }

    /**
     *
     * @param loop
     *            a loop.
     * @param block
     *            the block containing the loop.
     * @return the initializers if the loop is a for-loop, {@code null} otherwise.
     */
    private static StatementBlock getHeadStatement(LoopStatement loop, StatementBlock block) {
        final StatementBlock sb;
        if (loop != null && loop instanceof For) {
            ExtList headStatements = new ExtList();
            for (Statement statement : loop.getInitializers()) {
                headStatements.add(statement);
            }
            sb = new StatementBlock(headStatements);
        } else if (loop != null && loop instanceof While) {
            sb = null;
        } else {
            throw new IllegalArgumentException("Only blocks that begin with a while or a for "
                    + "loop may have a loop contract! \n" + "This block begins with "
                    + block.getFirstElement());
        }
        return sb;
    }

    /**
     *
     * @param loop
     *            a loop.
     * @param block
     *            the block containing the loop.
     * @param outerLabel
     *            the label to use for break statements.
     * @param innerLabel
     *            the label to use for continue statements.
     * @param loopLabels
     *            all labels belonging to the loop.
     * @param services
     *            services.
     * @return the loop's body. If the loop is a for-loop, it is transformed to a while-loop.
     * @see InnerBreakAndContinueReplacer
     */
    private static StatementBlock getBodyStatement(LoopStatement loop, StatementBlock block,
            Label outerLabel, Label innerLabel, List<Label> loopLabels, Services services) {
        final StatementBlock sb;
        if (loop != null && loop instanceof While) {
            if (loop.getBody() instanceof StatementBlock) {
                sb = (StatementBlock) loop.getBody();
            } else {
                sb = new StatementBlock(loop.getBody());
            }
        } else if (loop != null && loop instanceof For) {
            ExtList bodyStatements = new ExtList();
            bodyStatements.add(loop.getBody());
            StatementBlock innerBody = new InnerBreakAndContinueReplacer(
                    new StatementBlock(bodyStatements), loopLabels, outerLabel, innerLabel,
                    services).replace();

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
     * @param loop
     *            a loop.
     * @param block
     *            the block containing the loop.
     * @return all statements in the block after the loop.
     */
    private static StatementBlock getTailStatement(LoopStatement loop, StatementBlock block) {
        final StatementBlock sb;
        if (loop != null && (loop instanceof For || loop instanceof While)) {
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
    public While getLoop() {
        return loop;
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
        final OpReplacer replacer = new OpReplacer(replacementMap, services.getTermFactory());
        return replacer.replace(decreases);
    }

    @Override
    public Term getDecreases(Variables variables, Services services) {
        Map<ProgramVariable, ProgramVariable> map = createReplacementMap(variables, services);
        return new OpReplacer(map, services.getTermFactory()).replace(decreases);
    }

    @Override
    public ImmutableSet<FunctionalLoopContract> getFunctionalContracts() {
        return functionalContracts;
    }

    @Override
    public void setFunctionalLoopContract(FunctionalLoopContract contract) {
        assert contract.id() != Contract.INVALID_ID;
        assert contract.getLoopContract().equals(this);

        functionalContracts = DefaultImmutableSet.<FunctionalLoopContract> nil().add(contract);
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
            return "Loop Contract " + getBlock().getStartPosition().getLine() + " "
                    + getTarget().getUniqueName();
        } else {
            return "Loop Contract " + getBlock().getStartPosition().getLine() + " "
                    + Math.abs(getBlock().hashCode());
        }
    }

    @Override
    public String getDisplayName() {
        return "Loop Contract";
    }

    @Override
    public LoopContract update(final StatementBlock newBlock,
            final Map<LocationVariable, Term> newPreconditions,
            final Map<LocationVariable, Term> newPostconditions,
            final Map<LocationVariable, Term> newModifiesClauses,
            final ImmutableList<InfFlowSpec> newinfFlowSpecs, final Variables newVariables,
            final Term newMeasuredBy, final Term newDecreases) {
        return new SimpleLoopContract(baseName, newBlock, labels, method, modality,
                newPreconditions, newMeasuredBy, newPostconditions, newModifiesClauses,
                newinfFlowSpecs, newVariables, transactionApplicable, hasMod, newDecreases,
                functionalContracts, services);
    }

    @Override
    public LoopContract setBlock(StatementBlock newBlock) {
        return update(newBlock, preconditions, postconditions, modifiesClauses, infFlowSpecs,
                variables, measuredBy, decreases);
    }

    @Override
    public LoopContract setTarget(KeYJavaType newKJT, IObserverFunction newPM) {
        assert newPM instanceof IProgramMethod;
        assert newKJT.equals(newPM.getContainerType());
        return new SimpleLoopContract(baseName, block, labels, (IProgramMethod) newPM, modality,
                preconditions, measuredBy, postconditions, modifiesClauses, infFlowSpecs, variables,
                transactionApplicable, hasMod, decreases, functionalContracts, services);
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
     * This class is used to build {@link SimpleLoopContract}s.
     *
     * @see Creator#create()
     */
    public static class Creator extends AbstractBlockSpecificationElement.Creator<LoopContract> {

        /**
         * @see LoopContract#getDecreases()
         */
        private Term decreases;

        /**
         *
         * @param baseName
         *            the contract's base name.
         * @param block
         *            the block the contract belongs to.
         * @param labels
         *            all labels belonging to the block.
         * @param method
         *            the method containing the block.
         * @param behavior
         *            the contract's behavior.
         * @param variables
         *            the variables.
         * @param requires
         *            the contract's precondition.
         * @param measuredBy
         *            the contract's measured-by clause.
         * @param ensures
         *            the contracts postcondition due to normal termination.
         * @param infFlowSpecs
         *            the contract's information flow specifications.
         * @param breaks
         *            the contract's postconditions for abrupt termination with {@code break}
         *            statements.
         * @param continues
         *            the contract's postconditions for abrupt termination with {@code continue}
         *            statements.
         * @param returns
         *            the contract's postcondition for abrupt termination with {@code return}
         *            statements.
         * @param signals
         *            the contract's postcondition for abrupt termination due to abrupt termination.
         * @param signalsOnly
         *            a term specifying which uncaught exceptions may occur.
         * @param diverges
         *            a diverges clause.
         * @param assignables
         *            map from every heap to an assignable term.
         * @param hasMod
         *            map specifying on which heaps this contract has a modifies clause.
         * @param decreases
         *            the decreases term.
         * @param services
         *            services.
         */
        public Creator(String baseName, StatementBlock block, List<Label> labels,
                IProgramMethod method, Behavior behavior, Variables variables,
                Map<LocationVariable, Term> requires, Term measuredBy,
                Map<LocationVariable, Term> ensures, ImmutableList<InfFlowSpec> infFlowSpecs,
                Map<Label, Term> breaks, Map<Label, Term> continues, Term returns, Term signals,
                Term signalsOnly, Term diverges, Map<LocationVariable, Term> assignables,
                Map<LocationVariable, Boolean> hasMod, Term decreases, Services services) {
            super(baseName, block, labels, method, behavior, variables, requires, measuredBy,
                    ensures, infFlowSpecs, breaks, continues, returns, signals, signalsOnly,
                    diverges, assignables, hasMod, services);

            this.decreases = decreases;
        }

        @Override
        protected LoopContract build(String baseName, StatementBlock block, List<Label> labels,
                IProgramMethod method, Modality modality, Map<LocationVariable, Term> preconditions,
                Term measuredBy, Map<LocationVariable, Term> postconditions,
                Map<LocationVariable, Term> modifiesClauses,
                ImmutableList<InfFlowSpec> infFlowSpecs, Variables variables,
                boolean transactionApplicable, Map<LocationVariable, Boolean> hasMod) {
            return new SimpleLoopContract(baseName, block, labels, method, modality, preconditions,
                    measuredBy, postconditions, modifiesClauses, infFlowSpecs, variables,
                    transactionApplicable, hasMod, decreases, null, services);
        }

        @Override
        protected Map<LocationVariable, Term> buildPreconditions() {
            final Map<LocationVariable, Term> result = super.buildPreconditions();

            if (decreases != null) {
                for (Entry<LocationVariable, Term> entry : result.entrySet()) {
                    result.put(entry.getKey(), and(entry.getValue(), geq(decreases, zero())));
                }
            }

            return result;
        }
    }

    /**
     * This class is used to to combine multiple contracts for the same block and apply them
     * simultaneously.
     */
    protected static class Combinator
            extends AbstractBlockSpecificationElement.Combinator<LoopContract> {

        /**
         *
         * @param contracts
         *            the contracts to combine.
         * @param services
         *            services.
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
            String baseName = head.getBaseName();

            for (int i = 1; i < contracts.length; i++) {
                assert contracts[i].getBlock().equals(head.getBlock());

                baseName += SpecificationRepository.CONTRACT_COMBINATION_MARKER
                        + contracts[i].getBaseName();
            }

            placeholderVariables = head.getPlaceholderVariables();
            remembranceVariables = placeholderVariables.combineRemembranceVariables();

            ImmutableSet<FunctionalLoopContract> functionalContracts = DefaultImmutableSet.nil();

            for (LoopContract contract : contracts) {
                addConditionsFrom(contract);
                functionalContracts = functionalContracts.union(contract.getFunctionalContracts());
            }

            Map<LocationVariable, Boolean> hasMod = new LinkedHashMap<LocationVariable, Boolean>();
            for (LocationVariable heap : services.getTypeConverter().getHeapLDT().getAllHeaps()) {
                boolean hm = false;

                for (int i = 1; i < contracts.length && !hm; i++) {
                    hm = contracts[i].hasModifiesClause(heap);
                }
                hasMod.put(heap, hm);
            }

            SimpleLoopContract result = new SimpleLoopContract(baseName, head.getBlock(),
                    head.getLabels(), head.getMethod(), head.getModality(), preconditions,
                    contracts[0].getMby(), postconditions, modifiesClauses, head.getInfFlowSpecs(),
                    placeholderVariables, head.isTransactionApplicable(), hasMod,
                    contracts[0].getDecreases(), functionalContracts, services);

            return result;
        }
    }
}
