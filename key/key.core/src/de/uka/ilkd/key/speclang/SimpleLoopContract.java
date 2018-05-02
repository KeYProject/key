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
 */
public final class SimpleLoopContract
        extends AbstractBlockSpecificationElement implements LoopContract {

    private final Term decreases;

    private final StatementBlock head;
    private final Expression guard;
    private final StatementBlock body;
    private final StatementBlock tail;
    private final While loop;
    private final Services services;

    private final List<Label> loopLabels;

    private ImmutableSet<FunctionalLoopContract> functionalContracts;

    public SimpleLoopContract(final String baseName,
                               final StatementBlock block,
                               final List<Label> labels,
                               final IProgramMethod method,
                               final Modality modality,
                               final Map<LocationVariable, Term> preconditions,
                               final Term measuredBy,
                               final Map<LocationVariable, Term> postconditions,
                               final Map<LocationVariable, Term> modifiesClauses,
                               final ImmutableList<InfFlowSpec> infFlowSpecs,
                               final Variables variables,
                               final boolean transactionApplicable,
                               final Map<LocationVariable, Boolean> hasMod,
                               final Term decreases,
                               ImmutableSet<FunctionalLoopContract> functionalContracts,
                               Services services) {
        super(baseName,
                block,
                labels,
                method,
                modality,
                preconditions,
                measuredBy,
                postconditions,
                modifiesClauses,
                infFlowSpecs,
                variables,
                transactionApplicable,
                hasMod);

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
            throw new IllegalArgumentException(
                    "Only blocks that begin with a while or a for "
                    + "loop may have a loop contract! \n"
                    + "This block begins with " + block.getFirstElement());
        }

        head = getHeadStatement(loop, block);
        guard = loop.getGuardExpression();
        body = getBodyStatement(loop, block, outerLabel, innerLabel,
                                loopLabels, services);
        this.loop = new While(guard, body);
        tail = getTailStatement(loop, block);
    }


    public static LoopContract combine(ImmutableSet<LoopContract> contracts,
                                       Services services) {
        return new Combinator(
                contracts.toArray(new LoopContract[contracts.size()]),
                services)
                .combine();
    }

    private static StatementBlock getHeadStatement(LoopStatement loop,
                                                   StatementBlock block) {
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
            throw new IllegalArgumentException(
                    "Only blocks that begin with a while or a for "
                    + "loop may have a loop contract! \n"
                    + "This block begins with " + block.getFirstElement());
        }
        return sb;
    }

    private static StatementBlock getBodyStatement(LoopStatement loop,
                                                   StatementBlock block,
                                                   Label outerLabel,
                                                   Label innerLabel,
                                                   List<Label> loopLabels,
                                                   Services services) {
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
            StatementBlock innerBody =
                    new InnerBreakAndContinueReplacer(
                            new StatementBlock(bodyStatements),
                            loopLabels,
                            outerLabel,
                            innerLabel,
                            services).replace();

            ExtList updateStatements = new ExtList();
            for (Expression statement : loop.getUpdates()) {
                updateStatements.add(statement);
            }

            sb = new StatementBlock(
                    new StatementBlock(
                            new LabeledStatement(innerLabel, innerBody,
                                                 PositionInfo.UNDEFINED),
                            new StatementBlock(updateStatements)));
        } else {
            throw new IllegalArgumentException(
                    "Only blocks that begin with a while or a for "
                    + "loop may have a loop contract! \n"
                    + "This block begins with " + block.getFirstElement());
        }
        return sb;
    }

    private static StatementBlock getTailStatement(LoopStatement loop,
                                                   StatementBlock block) {
        final StatementBlock sb;
        if (loop != null
              && (loop instanceof For
                    || loop instanceof While)) {
            ExtList tailStatements = new ExtList();
            for (int i = 1; i < block.getStatementCount(); ++i) {
                tailStatements.add(block.getStatementAt(i));
            }
            sb = new StatementBlock(tailStatements);
        } else {
            throw new IllegalArgumentException(
                    "Only blocks that begin with a while or a for "
                    + "loop may have a loop contract! \n"
                    + "This block begins with " + block.getFirstElement());
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

        functionalContracts = DefaultImmutableSet.<FunctionalLoopContract>nil().add(contract);
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
            return "Loop Contract " + getBlock().getStartPosition().getLine() +
                    " " + getTarget().getUniqueName();
        } else {
            return "Loop Contract " + getBlock().getStartPosition().getLine() +
                    " " + Math.abs(getBlock().hashCode());
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
            final ImmutableList<InfFlowSpec> newinfFlowSpecs,
            final Variables newVariables,
            final Term newMeasuredBy, final Term newDecreases) {
        return new SimpleLoopContract(baseName, newBlock, labels, method, modality,
                newPreconditions, newMeasuredBy, newPostconditions,
                newModifiesClauses, newinfFlowSpecs,
                newVariables,
                transactionApplicable, hasMod, newDecreases,
                functionalContracts, services);
    }

    @Override
    public LoopContract setBlock(StatementBlock newBlock) {
        return update(newBlock, preconditions, postconditions, modifiesClauses,
                      infFlowSpecs, variables, measuredBy, decreases);
    }

    public LoopContract setTarget(KeYJavaType newKJT, IObserverFunction newPM) {
        assert newPM instanceof IProgramMethod;
        assert newKJT.equals(newPM.getContainerType());
        return new SimpleLoopContract(baseName, block, labels, (IProgramMethod)newPM, modality,
                                       preconditions, measuredBy, postconditions, modifiesClauses,
                                       infFlowSpecs, variables, transactionApplicable, hasMod,
                                       decreases, functionalContracts, services);
    }

    @Override
    public String toString() {
        return "SimpleLoopContract [block=" + block + ", labels=" + labels
                + ", method=" + method + ", modality=" + modality
                + ", instantiationSelf=" + instantiationSelf
                + ", preconditions=" + preconditions + ", postconditions="
                + postconditions + ", modifiesClauses=" + modifiesClauses
                + ", infFlowSpecs=" + infFlowSpecs
                + ", variables=" + variables
                + ", transactionApplicable=" + transactionApplicable
                + ", hasMod=" + hasMod + "]";
    }

    /**
     * This class is used to build {@link SimpleLoopContract}s.
     *
     * @see Creator#create()
     */
    public static class Creator
            extends AbstractBlockSpecificationElement.Creator<LoopContract> {

        private Term decreases;

        public Creator(String baseName, StatementBlock block,
                       List<Label> labels, IProgramMethod method, Behavior behavior,
                       Variables variables, Map<LocationVariable, Term> requires,
                       Term measuredBy, Map<LocationVariable, Term> ensures,
                       ImmutableList<InfFlowSpec> infFlowSpecs,
                       Map<Label, Term> breaks, Map<Label, Term> continues,
                       Term returns, Term signals, Term signalsOnly, Term diverges,
                       Map<LocationVariable, Term> assignables,
                       Map<LocationVariable, Boolean> hasMod, Term decreases, Services services) {
            super(baseName, block, labels, method, behavior, variables, requires,
                  measuredBy, ensures, infFlowSpecs, breaks, continues, returns, signals,
                  signalsOnly, diverges, assignables, hasMod, services);

            this.decreases = decreases;
        }

        @Override
        protected LoopContract build(String baseName,
                                     StatementBlock block,
                                     List<Label> labels,
                                     IProgramMethod method,
                                     Modality modality,
                                     Map<LocationVariable, Term> preconditions,
                                     Term measuredBy,
                                     Map<LocationVariable, Term> postconditions,
                                     Map<LocationVariable, Term> modifiesClauses,
                                     ImmutableList<InfFlowSpec> infFlowSpecs,
                                     Variables variables,
                                     boolean transactionApplicable,
                                     Map<LocationVariable, Boolean> hasMod) {
            return new SimpleLoopContract(
                    baseName, block, labels, method, modality, preconditions,
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

    protected static class Combinator
            extends AbstractBlockSpecificationElement.Combinator<LoopContract> {

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

            ImmutableSet<FunctionalLoopContract> functionalContracts =
                    DefaultImmutableSet.nil();

            for (LoopContract contract : contracts) {
                addConditionsFrom(contract);
                functionalContracts = functionalContracts.union(contract.getFunctionalContracts());
            }

            Map<LocationVariable, Boolean> hasMod = new LinkedHashMap<LocationVariable, Boolean>();
            for(LocationVariable heap : services.getTypeConverter().getHeapLDT().getAllHeaps()) {
                boolean hm = false;

                for (int i = 1; i < contracts.length && !hm; i++) {
                    hm = contracts[i].hasModifiesClause(heap);
                }
                hasMod.put(heap, hm);
            }

            SimpleLoopContract result =
                new SimpleLoopContract(baseName,
                                       head.getBlock(),
                                       head.getLabels(),
                                       head.getMethod(),
                                       head.getModality(),
                                       preconditions,
                                       contracts[0].getMby(),
                                       postconditions,
                                       modifiesClauses,
                                       head.getInfFlowSpecs(),
                                       placeholderVariables,
                                       head.isTransactionApplicable(),
                                       hasMod,
                                       contracts[0].getDecreases(),
                                       functionalContracts,
                                       services);

            return result;
        }
    }
}
