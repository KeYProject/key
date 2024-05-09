/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule;

import java.util.List;
import java.util.Map;

import de.uka.ilkd.key.informationflow.proof.InfFlowCheckInfo;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.label.TermLabelState;
import de.uka.ilkd.key.logic.op.JFunction;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.init.FunctionalBlockContractPO;
import de.uka.ilkd.key.proof.mgt.ComplexRuleJustificationBySpec;
import de.uka.ilkd.key.proof.mgt.RuleJustificationBySpec;
import de.uka.ilkd.key.rule.AuxiliaryContractBuilders.ConditionsAndClausesBuilder;
import de.uka.ilkd.key.rule.AuxiliaryContractBuilders.GoalsConfigurator;
import de.uka.ilkd.key.rule.AuxiliaryContractBuilders.UpdatesBuilder;
import de.uka.ilkd.key.rule.AuxiliaryContractBuilders.VariablesCreatorAndRegistrar;
import de.uka.ilkd.key.speclang.BlockContract;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.util.MiscTools;

import org.key_project.logic.Name;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSet;
import org.key_project.util.java.ArrayUtil;

import org.jspecify.annotations.NonNull;

/**
 * <p>
 * Rule for the application of {@link BlockContract}s.
 * </p>
 *
 * <p>
 * This splits the goal into two branches:
 * <ol>
 * <li>Precondition</li>
 * <li>Usage</li>
 * </ol>
 * </p>
 *
 * <p>
 * The validity of all {@link BlockContract}s that were used in the application of this rule must be
 * proven in a {@link FunctionalBlockContractPO} before the current proof is considered closed.
 * </p>
 *
 * @see BlockContractExternalBuiltInRuleApp
 *
 * @author lanzinger
 */
public final class BlockContractExternalRule extends AbstractBlockContractRule {

    /**
     * The only instance of this class.
     */
    public static final BlockContractExternalRule INSTANCE = new BlockContractExternalRule();

    /**
     * This rule's name.
     */
    private static final Name NAME = new Name("Block Contract (External)");

    /**
     * @see #getLastFocusTerm()
     */
    private Term lastFocusTerm;

    /**
     * @see #getLastInstantiation()
     */
    private Instantiation lastInstantiation;

    private BlockContractExternalRule() {
    }

    /**
     *
     * @param contract the contract being applied.
     * @param heaps the heaps.
     * @param localInVariables all free program variables in the block.
     * @param conditionsAndClausesBuilder a ConditionsAndClausesBuilder.
     * @param services services.
     * @return the preconditions.
     */
    private static Term[] createPreconditions(final Instantiation instantiation,
            final BlockContract contract, final List<LocationVariable> heaps,
            final ImmutableSet<ProgramVariable> localInVariables,
            final ConditionsAndClausesBuilder conditionsAndClausesBuilder,
            final Services services) {
        final Term precondition = conditionsAndClausesBuilder.buildPrecondition();
        final Term wellFormedHeapsCondition =
            conditionsAndClausesBuilder.buildWellFormedHeapsCondition();
        final Term reachableInCondition =
            conditionsAndClausesBuilder.buildReachableInCondition(localInVariables);
        final Term selfConditions = conditionsAndClausesBuilder.buildSelfConditions(heaps,
            contract.getMethod(), contract.getKJT(), instantiation.self(), services);
        return new Term[] { precondition, wellFormedHeapsCondition, reachableInCondition,
            selfConditions };
    }

    /**
     *
     * @param localOutVariables all free program variables modified by the block.
     * @param anonymisationHeaps the anonymization heaps.
     * @param conditionsAndClausesBuilder a ConditionsAndClausesBuilder.
     * @return the postconditions.
     */
    private static Term[] createAssumptions(final ImmutableSet<ProgramVariable> localOutVariables,
            final Map<LocationVariable, JFunction> anonymisationHeaps,
            final ConditionsAndClausesBuilder conditionsAndClausesBuilder) {
        final Term postcondition = conditionsAndClausesBuilder.buildPostcondition();
        final Term wellFormedAnonymisationHeapsCondition = conditionsAndClausesBuilder
                .buildWellFormedAnonymisationHeapsCondition(anonymisationHeaps);
        final Term reachableOutCondition =
            conditionsAndClausesBuilder.buildReachableOutCondition(localOutVariables);
        final Term atMostOneFlagSetCondition =
            conditionsAndClausesBuilder.buildAtMostOneFlagSetCondition();
        return new Term[] { postcondition, wellFormedAnonymisationHeapsCondition,
            reachableOutCondition, atMostOneFlagSetCondition };
    }

    /**
     *
     * @param contextUpdate the context update.
     * @param heaps the heaps.
     * @param anonymisationHeaps the anonymization heaps.
     * @param variables the variables.
     * @param services services.
     * @return the updates.
     */
    private static Term[] createUpdates(final Term contextUpdate,
            final List<LocationVariable> heaps,
            final Map<LocationVariable, JFunction> anonymisationHeaps,
            final BlockContract.Variables variables,
            final ConditionsAndClausesBuilder conditionsAndClausesBuilder,
            final Services services) {
        final Map<LocationVariable, Term> modifiesClauses =
            conditionsAndClausesBuilder.buildModifiesClauses();
        final UpdatesBuilder updatesBuilder = new UpdatesBuilder(variables, services);
        final Term remembranceUpdate = updatesBuilder.buildRemembranceUpdate(heaps);
        final Term anonymisationUpdate =
            updatesBuilder.buildAnonOutUpdate(anonymisationHeaps, modifiesClauses);
        final Term[] updates = new Term[] { contextUpdate, remembranceUpdate, anonymisationUpdate };
        return updates;
    }

    @Override
    public Term getLastFocusTerm() {
        return lastFocusTerm;
    }

    @Override
    protected void setLastFocusTerm(Term lastFocusTerm) {
        this.lastFocusTerm = lastFocusTerm;
    }

    @Override
    public Instantiation getLastInstantiation() {
        return lastInstantiation;
    }

    @Override
    public Name name() {
        return NAME;
    }

    @Override
    protected void setLastInstantiation(Instantiation lastInstantiation) {
        this.lastInstantiation = lastInstantiation;
    }

    @Override
    public IBuiltInRuleApp createApp(PosInOccurrence pos, TermServices services) {
        return new BlockContractExternalBuiltInRuleApp(this, pos);
    }

    @Override
    public boolean isApplicable(final Goal goal, final PosInOccurrence occurrence) {
        return !InfFlowCheckInfo.isInfFlow(goal) && super.isApplicable(goal, occurrence);
    }

    @Override
    public @NonNull ImmutableList<Goal> apply(final Goal goal, final Services services,
            final RuleApp ruleApp) throws RuleAbortException {
        assert ruleApp instanceof BlockContractExternalBuiltInRuleApp;
        BlockContractExternalBuiltInRuleApp application =
            (BlockContractExternalBuiltInRuleApp) ruleApp;

        if (InfFlowCheckInfo.isInfFlow(goal)) {
            throw new RuleAbortException(
                "BlockContractExternalRule does not support information flow goals!");
        }

        final Instantiation instantiation =
            instantiate(application.posInOccurrence().subTerm(), goal, services);
        final BlockContract contract = application.getContract();
        contract.setInstantiationSelf(instantiation.self());
        assert contract.getBlock().equals(instantiation.statement());

        final List<LocationVariable> heaps = application.getHeapContext();
        final ImmutableSet<ProgramVariable> localInVariables =
            MiscTools.getLocalIns(instantiation.statement(), services);
        final ImmutableSet<ProgramVariable> localOutVariables =
            MiscTools.getLocalOuts(instantiation.statement(), services);
        final Map<LocationVariable, JFunction> anonymisationHeaps =
            createAndRegisterAnonymisationVariables(heaps, contract, services);
        final BlockContract.Variables variables =
            new VariablesCreatorAndRegistrar(goal, contract.getPlaceholderVariables(), services)
                    .createAndRegister(instantiation.self(), true);

        final ConditionsAndClausesBuilder conditionsAndClausesBuilder =
            new ConditionsAndClausesBuilder(contract, heaps, variables, instantiation.self(),
                services);
        final Term[] preconditions = createPreconditions(instantiation, contract, heaps,
            localInVariables, conditionsAndClausesBuilder, services);
        final Term[] assumptions =
            createAssumptions(localOutVariables, anonymisationHeaps, conditionsAndClausesBuilder);
        final Term freePostcondition = conditionsAndClausesBuilder.buildFreePostcondition();
        final Term[] updates = createUpdates(instantiation.update(), heaps, anonymisationHeaps,
            variables, conditionsAndClausesBuilder, services);

        final ImmutableList<Goal> result;
        final GoalsConfigurator configurator =
            new GoalsConfigurator(application, new TermLabelState(), instantiation,
                contract.getLabels(), variables, application.posInOccurrence(), services, this);
        result = goal.split(2);
        configurator.setUpPreconditionGoal(result.tail().head(), updates[0], preconditions);
        configurator.setUpUsageGoal(result.head(), updates,
            ArrayUtil.add(assumptions, freePostcondition));

        final ComplexRuleJustificationBySpec cjust = (ComplexRuleJustificationBySpec) goal.proof()
                .getInitConfig().getJustifInfo().getJustification(this);
        for (Contract c : contract.getFunctionalContracts()) {
            cjust.add(application, new RuleJustificationBySpec(c));
        }

        return result;
    }
}
