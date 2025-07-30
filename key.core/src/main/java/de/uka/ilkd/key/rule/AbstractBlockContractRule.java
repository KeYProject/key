/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule;

import java.util.LinkedHashMap;
import java.util.Map;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.statement.JavaStatement;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.FunctionalBlockContractPO;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.proof.mgt.SpecificationRepository;
import de.uka.ilkd.key.speclang.BlockContract;

import org.key_project.logic.Name;
import org.key_project.logic.op.Function;
import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableSet;

import org.jspecify.annotations.Nullable;

/**
 * <p>
 * Rule for the application of {@link BlockContract}s.
 * </p>
 *
 * @see AbstractBlockContractBuiltInRuleApp
 *
 * @author wacker, lanzinger
 */
public abstract class AbstractBlockContractRule extends AbstractAuxiliaryContractRule {

    /**
     *
     * @param instantiation an instantiation.
     * @param goal the current goal.
     * @param services services.
     * @return all applicable block contracts for the instantiation.
     */
    public static @Nullable ImmutableSet<BlockContract> getApplicableContracts(
            final Instantiation instantiation, final Goal goal, final Services services) {
        if (instantiation == null) {
            return DefaultImmutableSet.nil();
        }
        return getApplicableContracts(services.getSpecificationRepository(),
            instantiation.statement(), instantiation.modality().kind(), goal);
    }

    /**
     * @param specifications a specification repository.
     * @param statement a block.
     * @param modalityKind the current goal's modality.
     * @param goal the current goal.
     * @return all applicable block contracts for the block from the repository.
     */
    public static @Nullable ImmutableSet<BlockContract> getApplicableContracts(
            final SpecificationRepository specifications, final JavaStatement statement,
            final JModality.JavaModalityKind modalityKind, final Goal goal) {
        if (statement instanceof StatementBlock block) {

            ImmutableSet<BlockContract> collectedContracts =
                specifications.getBlockContracts(block, modalityKind);
            if (modalityKind == JModality.JavaModalityKind.BOX) {
                collectedContracts =
                    collectedContracts.union(
                        specifications.getBlockContracts(block, JModality.JavaModalityKind.DIA));
            } else if (modalityKind == JModality.JavaModalityKind.BOX_TRANSACTION) {
                collectedContracts = collectedContracts
                        .union(specifications.getBlockContracts(block,
                            JModality.JavaModalityKind.DIA_TRANSACTION));
            }
            return filterAppliedContracts(collectedContracts, goal);
        } else {
            return null;
        }
    }

    /**
     *
     * @param collectedContracts a set of block contracts.
     * @param goal the current goal.
     * @return the set with all non-applicable contracts filtered out.
     */
    protected static ImmutableSet<BlockContract> filterAppliedContracts(
            final ImmutableSet<BlockContract> collectedContracts, final Goal goal) {
        ImmutableSet<BlockContract> result = DefaultImmutableSet.nil();
        for (BlockContract contract : collectedContracts) {
            if (!contractApplied(contract, goal) /* || InfFlowCheckInfo.isInfFlow(goal) */) {
                result = result.add(contract);
            }
        }
        return result;
    }

    /**
     *
     * @param contract a block contract.
     * @param goal the current goal.
     * @return {@code true} if the contract has already been applied.
     */
    protected static boolean contractApplied(final BlockContract contract, final Goal goal) {
        final var po = getAppliedProofObligation(contract, goal);
        if (po == null)
            return true;

        return po instanceof FunctionalBlockContractPO functionalBlockContractPO
                && contract.getBlock().equals(functionalBlockContractPO.getBlock());
    }

    /// Searches backwards for a [{@link BlockContractInternalBuiltInRuleApp] on the parent path of
    /// `goal`.
    /// @param contract a block contract.
    /// @param goal the current goal.
    /// @return the proof obligation for the contract on the proof if the contract has already been
    /// applied,
    /// otherwise `null`.
    protected static @Nullable ProofOblInput getAppliedProofObligation(BlockContract contract,
            Goal goal) {
        Node selfOrParentNode = goal.node();
        Node previousNode = null;
        while (selfOrParentNode != null) {
            RuleApp app = selfOrParentNode.getAppliedRuleApp();
            if (app instanceof BlockContractInternalBuiltInRuleApp blockRuleApp) {
                if (blockRuleApp.getStatement().equals(contract.getBlock())
                        && selfOrParentNode.getChildNr(previousNode) == 0) {
                    // prevent application of contract in its own check validity branch
                    // but not in other branches, e.g., do-while
                    // loops might need to apply the same contract
                    // twice in its usage branch
                    return null;
                }
            }
            previousNode = selfOrParentNode;
            selfOrParentNode = selfOrParentNode.parent();
        }

        Services services = goal.proof().getServices();
        Proof proof = goal.proof();
        return services.getSpecificationRepository().getProofOblInput(proof);
    }

    /**
     *
     * @param variables variables.
     * @param contract a block contract.
     * @param services services.
     * @return a map from every variable that is changed in the block to its anonymization constant.
     */
    protected static Map<LocationVariable, Function> createAndRegisterAnonymisationVariables(
            final Iterable<LocationVariable> variables, final BlockContract contract,
            final TermServices services) {
        Map<LocationVariable, Function> result = new LinkedHashMap<>(40);
        final TermBuilder tb = services.getTermBuilder();
        for (LocationVariable variable : variables) {
            if (contract.hasModifiableClause(variable)) {
                final String anonymisationName =
                    tb.newName(AuxiliaryContractBuilders.ANON_OUT_PREFIX + variable.name());
                final Function anonymisationFunction =
                    new JFunction(new Name(anonymisationName), variable.sort(), true);
                services.getNamespaces().functions().addSafely(anonymisationFunction);
                result.put(variable, anonymisationFunction);
            }
        }
        return result;
    }


    @Override
    public boolean isApplicable(final Goal goal, final PosInOccurrence occurrence) {
        if (occursNotAtTopLevelInSuccedent(occurrence)) {
            return false;
        }
        // abort if inside of transformer
        if (Transformer.inTransformer(occurrence)) {
            return false;
        }
        final Instantiation instantiation =
            instantiate((JTerm) occurrence.subTerm(), goal);
        if (instantiation == null) {
            return false;
        }
        final ImmutableSet<BlockContract> contracts =
            getApplicableContracts(instantiation, goal, goal.proof().getServices());
        return !contracts.isEmpty();
    }

    /**
     * @param formula the formula on which the rule is to be applied.
     * @param goal the current goal.
     * @return a new instantiation.
     */
    public Instantiation instantiate(final JTerm formula, final Goal goal) {
        if (formula == getLastFocusTerm()) {
            return getLastInstantiation();
        } else {
            final Instantiation result = new Instantiator(formula, goal).instantiate();
            setLastFocusTerm(formula);
            setLastInstantiation(result);
            return result;
        }
    }

    /**
     * A builder for {@link Instantiation}s.
     */
    protected static final class Instantiator extends AbstractAuxiliaryContractRule.Instantiator {

        /**
         *
         * @param formula the formula on which the rule is to be applied.
         * @param goal the current goal.
         */
        public Instantiator(final JTerm formula, final Goal goal) {
            super(formula, goal);
        }

        @Override
        protected boolean hasApplicableContracts(final Services services,
                final JavaStatement statement, final JModality.JavaModalityKind modalityKind,
                Goal goal) {
            ImmutableSet<BlockContract> contracts = getApplicableContracts(
                services.getSpecificationRepository(), statement, modalityKind, goal);

            return contracts != null && !contracts.isEmpty();
        }
    }

    public static class BlockContractHint {
        protected final static BlockContractHint USAGE_BRANCH =
            new BlockContractHint("Usage Branch");

        private final ProgramVariable excVar;

        private final String description;

        public BlockContractHint(String description) {
            this.description = description;
            this.excVar = null;
        }

        public BlockContractHint(String description, ProgramVariable excVar) {
            this.description = description;
            this.excVar = excVar;
        }

        public static BlockContractHint createUsageBranchHint() {
            return USAGE_BRANCH;
        }

        public static BlockContractHint createValidityBranchHint(ProgramVariable excVar) {
            return new BlockContractHint("Validity Branch", excVar);
        }

        public ProgramVariable getExceptionalVariable() {
            return excVar;
        }

        public String getDescription() {
            return description;
        }

        @Override
        public String toString() {
            return description
                    + (excVar != null ? "Validity Branch: exceptionVar=" + excVar.name() : "");
        }
    }
}
