/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule;

import java.util.LinkedHashMap;
import java.util.Map;

import de.uka.ilkd.key.informationflow.po.SymbolicExecutionPO;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.statement.JavaStatement;
import de.uka.ilkd.key.java.statement.LoopStatement;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.proof.mgt.SpecificationRepository;
import de.uka.ilkd.key.speclang.LoopContract;

import org.key_project.logic.Name;
import org.key_project.logic.op.Function;
import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableSet;

/**
 * <p>
 * Rule for the application of {@link LoopContract}s.
 * </p>
 *
 * @see AbstractLoopContractBuiltInRuleApp
 *
 * @author lanzinger
 */
public abstract class AbstractLoopContractRule extends AbstractAuxiliaryContractRule {

    /**
     *
     * @param instantiation an instantiation.
     * @param goal the current goal.
     * @param services services.
     * @return all applicable loop contracts for the instantiation.
     */
    public static ImmutableSet<LoopContract> getApplicableContracts(
            final Instantiation instantiation, final Goal goal, final Services services) {
        if (instantiation == null) {
            return DefaultImmutableSet.nil();
        }
        return getApplicableContracts(services.getSpecificationRepository(),
            instantiation.statement(), instantiation.modality().kind(), goal);
    }

    /**
     * @param specifications a specification repository.
     * @param statement a statement.
     * @param modalityKind the current goal's modality.
     * @param goal the current goal.
     * @return all applicable loop contracts for the block from the repository.
     */
    public static ImmutableSet<LoopContract> getApplicableContracts(
            final SpecificationRepository specifications, final JavaStatement statement,
            final JModality.JavaModalityKind modalityKind, final Goal goal) {
        ImmutableSet<LoopContract> collectedContracts;

        if (statement instanceof StatementBlock block) {

            collectedContracts = specifications.getLoopContracts(block, modalityKind);
            if (modalityKind == JModality.JavaModalityKind.BOX) {
                collectedContracts =
                    collectedContracts.union(
                        specifications.getLoopContracts(block, JModality.JavaModalityKind.DIA));
            } else if (modalityKind == JModality.JavaModalityKind.BOX_TRANSACTION) {
                collectedContracts = collectedContracts
                        .union(specifications.getLoopContracts(block,
                            JModality.JavaModalityKind.DIA_TRANSACTION));
            }
        } else {
            LoopStatement loop = (LoopStatement) statement;

            collectedContracts = specifications.getLoopContracts(loop, modalityKind);
            if (modalityKind == JModality.JavaModalityKind.BOX) {
                collectedContracts =
                    collectedContracts.union(
                        specifications.getLoopContracts(loop, JModality.JavaModalityKind.DIA));
            } else if (modalityKind == JModality.JavaModalityKind.BOX_TRANSACTION) {
                collectedContracts = collectedContracts
                        .union(specifications.getLoopContracts(loop,
                            JModality.JavaModalityKind.DIA_TRANSACTION));
            }
        }

        return filterAppliedContracts(collectedContracts, goal);
    }

    /**
     *
     * @param collectedContracts a set of loop contracts.
     * @param goal the current goal.
     * @return the set with all non-applicable contracts filtered out.
     */
    protected static ImmutableSet<LoopContract> filterAppliedContracts(
            final ImmutableSet<LoopContract> collectedContracts, final Goal goal) {
        ImmutableSet<LoopContract> result = DefaultImmutableSet.nil();
        for (LoopContract contract : collectedContracts) {
            if (!contractApplied(contract, goal)) {
                result = result.add(contract);
            }
        }
        return result;
    }

    /**
     *
     * @param contract a loop contract.
     * @param goal the current goal.
     * @return {@code true} if the contract has already been applied.
     */
    protected static boolean contractApplied(final LoopContract contract, final Goal goal) {
        Node selfOrParentNode = goal.node();
        Node previousNode = null;
        while (selfOrParentNode != null) {
            RuleApp app = selfOrParentNode.getAppliedRuleApp();
            if (app instanceof LoopContractInternalBuiltInRuleApp blockRuleApp) {
                if ((contract.isOnBlock() && blockRuleApp.getStatement().equals(contract.getBlock())
                        || !contract.isOnBlock()
                                && blockRuleApp.getStatement().equals(contract.getLoop()))
                        && selfOrParentNode.getChildNr(previousNode) == 0) {
                    // prevent application of contract in its own check validity branch
                    // but not in other branches, e.g., do-while
                    // loops might need to apply the same contract
                    // twice in its usage branch
                    return true;
                }
            }
            previousNode = selfOrParentNode;
            selfOrParentNode = selfOrParentNode.parent();
        }

        Services services = goal.proof().getServices();
        Proof proof = goal.proof();
        ProofOblInput po = services.getSpecificationRepository().getProofOblInput(proof);
        if (po instanceof SymbolicExecutionPO) {
            Goal initiatingGoal = ((SymbolicExecutionPO) po).getInitiatingGoal();
            return contractApplied(contract, initiatingGoal);
        } else {
            return false;
        }
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

        final ImmutableSet<LoopContract> contracts =
            getApplicableContracts(instantiation, goal, goal.proof().getServices());

        for (LoopContract contract : contracts) {
            // The rule is only applicable if
            // (a) the block starts with a while loop or
            // (b) the block starts with a for loop whose head has already been applied
            // via the rule LoopContractApplyHead.
            if (contract.getHead() == null) {
                return true;
            }
        }
        return false;
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
     *
     * @param variables variables.
     * @param contract a loop contract.
     * @param services services.
     * @return a map from every variable that is changed in the block to its anonymization constant.
     */
    protected Map<LocationVariable, Function> createAndRegisterAnonymisationVariables(
            final Iterable<LocationVariable> variables, final LoopContract contract,
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

    /**
     * A builder for {@link Instantiation}s.
     */
    protected static final class Instantiator extends AbstractAuxiliaryContractRule.Instantiator {

        /**
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
            ImmutableSet<LoopContract> contracts = getApplicableContracts(
                services.getSpecificationRepository(), statement, modalityKind, goal);

            return contracts != null && !contracts.isEmpty();
        }
    }
}
