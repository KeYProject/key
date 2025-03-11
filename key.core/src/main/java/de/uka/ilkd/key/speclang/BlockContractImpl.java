/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.speclang;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.function.UnaryOperator;

import de.uka.ilkd.key.java.Label;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.proof.mgt.SpecificationRepository;
import de.uka.ilkd.key.speclang.jml.pretranslation.Behavior;
import de.uka.ilkd.key.util.InfFlowSpec;

import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSet;
import org.key_project.util.java.MapUtil;

/**
 * Default implementation of {@link BlockContract}.
 *
 * @see BlockContractImpl.Creator
 *
 * @author wacker, lanzinger
 */
public final class BlockContractImpl extends AbstractAuxiliaryContractImpl
        implements BlockContract {

    /**
     * @see #toLoopContract()
     */
    private LoopContract loopContract = null;

    /**
     * @param baseName the base name.
     * @param block the block this contract belongs to.
     * @param labels all labels belonging to the block.
     * @param method the method containing the block.
     * @param modalityKind this contract's modality.
     * @param preconditions this contract's preconditions on every heap.
     * @param measuredBy this contract's measured-by term.
     * @param postconditions this contract's postconditions on every heap.
     * @param modifiableClauses this contract's modifiable clauses on every heap.
     * @param freeModifiableClauses this contract's free modifiable clauses on every heap.
     * @param infFlowSpecs this contract's information flow specifications.
     * @param variables this contract's variables.
     * @param transactionApplicable whether or not this contract is applicable for transactions.
     * @param hasModifiable a map specifying on which heaps this contract has a modifiable clause.
     * @param hasFreeModifiable a map specifying on which heaps this contract has a free modifiable
     *        clause.
     * @param functionalContracts the functional contracts corresponding to this contract.
     */
    public BlockContractImpl(final String baseName, final StatementBlock block,
            final List<Label> labels, final IProgramMethod method,
            final Modality.JavaModalityKind modalityKind,
            final Map<LocationVariable, Term> preconditions,
            final Map<LocationVariable, Term> freePreconditions, final Term measuredBy,
            final Map<LocationVariable, Term> postconditions,
            final Map<LocationVariable, Term> freePostconditions,
            final Map<LocationVariable, Term> modifiableClauses,
            final Map<LocationVariable, Term> freeModifiableClauses,
            final ImmutableList<InfFlowSpec> infFlowSpecs, final Variables variables,
            final boolean transactionApplicable, final Map<LocationVariable, Boolean> hasModifiable,
            final Map<LocationVariable, Boolean> hasFreeModifiable,
            ImmutableSet<FunctionalAuxiliaryContract<?>> functionalContracts) {
        super(baseName, block, labels, method, modalityKind,
            preconditions, freePreconditions, measuredBy, postconditions, freePostconditions,
            modifiableClauses, freeModifiableClauses, infFlowSpecs, variables,
            transactionApplicable,
            hasModifiable, hasFreeModifiable, functionalContracts);
    }

    /**
     *
     * @param contracts a set of block contracts to combine.
     * @param services services.
     * @return the combination of the specified block contracts.
     */
    public static BlockContract combine(ImmutableSet<BlockContract> contracts, Services services) {
        return new Combinator(contracts.toArray(new BlockContract[contracts.size()]), services)
                .combine();
    }

    /**
     *
     * @param loopContract the loop contract from which this block contract was created.
     * @see #toLoopContract()
     */
    void setLoopContract(LoopContract loopContract) {
        if (this.loopContract != null) {
            throw new IllegalStateException();
        }

        this.loopContract = loopContract;
    }

    @Override
    public LoopContract toLoopContract() {
        return loopContract;
    }

    @Override
    public void setFunctionalContract(FunctionalAuxiliaryContract<?> contract) {
        super.setFunctionalContract(contract);

        if (loopContract != null) {
            loopContract.setFunctionalContract(contract);
        }
    }

    @Override
    public void visit(final Visitor visitor) {
        assert visitor != null;
        visitor.performActionOnBlockContract(this);
    }

    @Override
    public String getName() {
        return "Block Contract";
    }

    @Override
    public String getUniqueName() {
        if (getTarget() != null) {
            return "Block Contract " + getBlock().getStartPosition().line() + " "
                + getTarget().getUniqueName();
        } else {
            return "Block Contract " + getBlock().getStartPosition().line() + " "
                + Math.abs(getBlock().hashCode());
        }
    }

    @Override
    public String getDisplayName() {
        return "Block Contract";
    }

    @Override
    public BlockContract map(UnaryOperator<Term> op, Services services) {
        Map<LocationVariable, Term> newPreconditions = preconditions.entrySet().stream()
                .collect(MapUtil.collector(Map.Entry::getKey, entry -> op.apply(entry.getValue())));
        Map<LocationVariable, Term> newFreePreconditions = freePreconditions.entrySet().stream()
                .collect(MapUtil.collector(Map.Entry::getKey, entry -> op.apply(entry.getValue())));
        Map<LocationVariable, Term> newPostconditions = postconditions.entrySet().stream()
                .collect(MapUtil.collector(Map.Entry::getKey, entry -> op.apply(entry.getValue())));
        Map<LocationVariable, Term> newFreePostconditions = freePostconditions.entrySet().stream()
                .collect(MapUtil.collector(Map.Entry::getKey, entry -> op.apply(entry.getValue())));
        Map<LocationVariable, Term> newModifiableClauses = modifiableClauses.entrySet().stream()
                .collect(MapUtil.collector(Map.Entry::getKey, entry -> op.apply(entry.getValue())));
        Map<LocationVariable, Term> newFreeModifiableClauses = freeModifiableClauses.entrySet()
                .stream()
                .collect(MapUtil.collector(Map.Entry::getKey, entry -> op.apply(entry.getValue())));
        Term newMeasuredBy = op.apply(measuredBy);

        return update(block, newPreconditions, newFreePreconditions, newPostconditions,
            newFreePostconditions, newModifiableClauses, newFreeModifiableClauses,
            infFlowSpecs.stream().map(spec -> spec.map(op)).collect(ImmutableList.collector()),
            variables, newMeasuredBy);
    }

    @Override
    public BlockContract update(final StatementBlock newBlock,
            final Map<LocationVariable, Term> newPreconditions,
            final Map<LocationVariable, Term> newFreePreconditions,
            final Map<LocationVariable, Term> newPostconditions,
            final Map<LocationVariable, Term> newFreePostconditions,
            final Map<LocationVariable, Term> newModifiableClauses,
            final Map<LocationVariable, Term> newFreeModifiableClauses,
            final ImmutableList<InfFlowSpec> newinfFlowSpecs, final Variables newVariables,
            Term newMeasuredBy) {
        BlockContractImpl result = new BlockContractImpl(baseName, newBlock, labels, method,
            modalityKind, newPreconditions, newFreePreconditions, newMeasuredBy, newPostconditions,
            newFreePostconditions, newModifiableClauses, newFreeModifiableClauses, newinfFlowSpecs,
            newVariables, transactionApplicable, hasModifiable, hasFreeModifiable,
            getFunctionalContracts());
        result.setLoopContract(loopContract);
        return result;
    }

    @Override
    public BlockContract setBlock(StatementBlock newBlock) {
        return update(newBlock, preconditions, freePreconditions, postconditions,
            freePostconditions, modifiableClauses, freeModifiableClauses, infFlowSpecs,
            variables, measuredBy);
    }

    @Override
    public BlockContract setTarget(KeYJavaType newKJT, IObserverFunction newPM) {
        assert newPM instanceof IProgramMethod;
        assert newKJT.equals(newPM.getContainerType());
        BlockContractImpl result = new BlockContractImpl(baseName, block, labels,
            (IProgramMethod) newPM, modalityKind, preconditions, freePreconditions, measuredBy,
            postconditions, freePostconditions, modifiableClauses, freeModifiableClauses,
            infFlowSpecs,
            variables, transactionApplicable, hasModifiable, hasFreeModifiable,
            getFunctionalContracts());
        result.setLoopContract(loopContract);
        return result;
    }

    @Override
    public String toString() {
        return "SimpleBlockContract [block=" + block + ", labels=" + labels + ", method=" + method
            + ", modality=" + modalityKind + ", instantiationSelf=" + instantiationSelf
            + ", preconditions=" + preconditions + ", postconditions=" + postconditions
            + ", modifiableClauses=" + modifiableClauses + ", infFlowSpecs=" + infFlowSpecs
            + ", variables=" + variables + ", transactionApplicable=" + transactionApplicable
            + ", hasModifiable=" + hasModifiable + "]";
    }

    /**
     * This class is used to build {@link BlockContractImpl}s.
     *
     * @see Creator#create()
     */
    public static class Creator extends AbstractAuxiliaryContractImpl.Creator<BlockContract> {

        /**
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
         * @param modifiables map from every heap to an modifiable term.
         * @param hasModifiable map specifying on which heaps this contract has a modifiable clause.
         * @param services services.
         */
        public Creator(String baseName, StatementBlock block, List<Label> labels,
                IProgramMethod method, Behavior behavior, Variables variables,
                Map<LocationVariable, Term> requires, Map<LocationVariable, Term> requiresFree,
                Term measuredBy, Map<LocationVariable, Term> ensures,
                Map<LocationVariable, Term> ensuresFree, ImmutableList<InfFlowSpec> infFlowSpecs,
                Map<Label, Term> breaks, Map<Label, Term> continues, Term returns, Term signals,
                Term signalsOnly, Term diverges, Map<LocationVariable, Term> modifiables,
                Map<LocationVariable, Term> modifiablesFree,
                Map<LocationVariable, Boolean> hasModifiable,
                Map<LocationVariable, Boolean> hasFreeModifiable,
                Services services) {
            super(baseName, block, labels, method, behavior, variables,
                requires, requiresFree, measuredBy, ensures, ensuresFree,
                infFlowSpecs, breaks, continues, returns, signals, signalsOnly,
                diverges, modifiables, modifiablesFree, hasModifiable, hasFreeModifiable, services);
        }

        @Override
        protected BlockContract build(String baseName, StatementBlock block, List<Label> labels,
                IProgramMethod method, Modality.JavaModalityKind modalityKind,
                Map<LocationVariable, Term> preconditions,
                Map<LocationVariable, Term> freePreconditions, Term measuredBy,
                Map<LocationVariable, Term> postconditions,
                Map<LocationVariable, Term> freePostconditions,
                Map<LocationVariable, Term> modifiableClauses,
                Map<LocationVariable, Term> freeModifiableClauses,
                ImmutableList<InfFlowSpec> infFlowSpecs, Variables variables,
                boolean transactionApplicable, Map<LocationVariable, Boolean> hasModifiable,
                Map<LocationVariable, Boolean> hasFreeModifiable) {
            return new BlockContractImpl(baseName, block, labels, method, modalityKind,
                preconditions, freePreconditions, measuredBy,
                postconditions, freePostconditions, modifiableClauses, freeModifiableClauses,
                infFlowSpecs, variables, transactionApplicable, hasModifiable, hasFreeModifiable,
                null);
        }
    }

    /**
     * This class is used to to combine multiple contracts for the same block and apply them
     * simultaneously.
     */
    protected static class Combinator
            extends AbstractAuxiliaryContractImpl.Combinator<BlockContract> {

        /**
         *
         * @param contracts the contracts to combine.
         * @param services services.
         */
        public Combinator(BlockContract[] contracts, Services services) {
            super(contracts, services);
        }

        @Override
        protected BlockContract combine() {
            assert contracts.length > 0;
            if (contracts.length == 1) {
                return contracts[0];
            }

            final BlockContract head = contracts[0];
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

            for (BlockContract contract : contracts) {
                addConditionsFrom(contract);
                functionalContracts = functionalContracts.union(contract.getFunctionalContracts());
            }

            Map<LocationVariable, Boolean> hasModifiable = new LinkedHashMap<>();
            Map<LocationVariable, Boolean> hasFreeModifiable =
                new LinkedHashMap<LocationVariable, Boolean>();
            for (LocationVariable heap : services.getTypeConverter().getHeapLDT().getAllHeaps()) {
                boolean hm = false;
                boolean hfm = false;

                for (int i = 1; i < contracts.length && !hm && !hfm; i++) {
                    hm |= contracts[i].hasModifiableClause(heap);
                    hfm |= contracts[i].hasFreeModifiableClause(heap);
                }
                hasModifiable.put(heap, hm);
                hasFreeModifiable.put(heap, hm);
            }


            BlockContractImpl result = new BlockContractImpl(baseName.toString(), head.getBlock(),
                head.getLabels(), head.getMethod(), head.getModalityKind(),
                preconditions, freePreconditions,
                contracts[0].getMby(), postconditions, freePostconditions,
                modifiableClauses, freeModifiableClauses, head.getInfFlowSpecs(),
                placeholderVariables, head.isTransactionApplicable(), hasModifiable,
                hasFreeModifiable,
                functionalContracts);

            return result;
        }
    }
}
