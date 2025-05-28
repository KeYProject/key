/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule;

import java.util.List;
import java.util.Map;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.label.TermLabelState;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.AuxiliaryContractBuilders.ConditionsAndClausesBuilder;
import de.uka.ilkd.key.rule.AuxiliaryContractBuilders.GoalsConfigurator;
import de.uka.ilkd.key.rule.AuxiliaryContractBuilders.UpdatesBuilder;
import de.uka.ilkd.key.rule.AuxiliaryContractBuilders.VariablesCreatorAndRegistrar;
import de.uka.ilkd.key.speclang.AuxiliaryContract;
import de.uka.ilkd.key.speclang.LoopContract;
import de.uka.ilkd.key.util.MiscTools;

import org.key_project.logic.Name;
import org.key_project.logic.op.Function;
import org.key_project.prover.rules.RuleAbortException;
import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSet;
import org.key_project.util.java.ArrayUtil;

import org.jspecify.annotations.NonNull;

/**
 * <p>
 * Rule for the application of {@link LoopContract}s.
 * </p>
 *
 * <p>
 * This splits the goal into two branches:
 * <ol>
 * <li>Validity</li>
 * <li>Precondition</li>
 * <li>Usage</li>
 * </ol>
 * </p>
 *
 * @see LoopContractInternalBuiltInRuleApp
 *
 * @author lanzinger
 */
public final class LoopContractInternalRule extends AbstractLoopContractRule {

    /**
     * The only instance of this class.
     */
    public static final LoopContractInternalRule INSTANCE = new LoopContractInternalRule();

    /**
     * This rule's name.
     */
    private static final Name NAME = new Name("Loop Contract (Internal)");

    /**
     * @see #getLastFocusTerm()
     */
    private JTerm lastFocusTerm;

    /**
     * @see #getLastInstantiation()
     */
    private Instantiation lastInstantiation;

    private LoopContractInternalRule() {
    }

    /**
     * Creates preconditions.
     *
     * @param selfTerm the self term.
     * @param contract the loop contract being applied.
     * @param heaps the heaps.
     * @param localInVariables all free program variables in the block.
     * @param conditionsAndClausesBuilder a ConditionsAndClausesBuilder.
     * @param services services.
     * @return the preconditions.
     */
    private static JTerm[] createPreconditions(final JTerm selfTerm, final LoopContract contract,
            final List<LocationVariable> heaps,
            final ImmutableSet<LocationVariable> localInVariables,
            final ConditionsAndClausesBuilder conditionsAndClausesBuilder,
            final Services services) {
        final JTerm precondition = conditionsAndClausesBuilder.buildPrecondition();
        final JTerm wellFormedHeapsCondition =
            conditionsAndClausesBuilder.buildWellFormedHeapsCondition();
        final JTerm reachableInCondition =
            conditionsAndClausesBuilder.buildReachableInCondition(localInVariables);
        final JTerm selfConditions = conditionsAndClausesBuilder.buildSelfConditions(heaps,
            contract.getMethod(), contract.getKJT(), selfTerm, services);
        return new JTerm[] { precondition, wellFormedHeapsCondition, reachableInCondition,
            selfConditions };
    }

    /**
     * Creates postconditions for the current loop iteration.
     *
     * @param modifiableClauses the loop's modifiable clauses.
     * @param freeModifiableClauses the loop's free modifiable clauses.
     * @param conditionsAndClausesBuilder ConditionsAndClausesBuilder.
     * @return the postconditions for the current loop iteration.
     */
    private static JTerm[] createPostconditions(
            final Map<LocationVariable, JTerm> modifiableClauses,
            final Map<LocationVariable, JTerm> freeModifiableClauses,
            final ConditionsAndClausesBuilder conditionsAndClausesBuilder) {
        final JTerm postcondition = conditionsAndClausesBuilder.buildPostcondition();
        final JTerm frameCondition =
            conditionsAndClausesBuilder.buildFrameCondition(
                modifiableClauses, freeModifiableClauses);
        return new JTerm[] { postcondition, frameCondition };
    }



    /**
     * Creates postconditions for the next loop iteration.
     *
     * @param selfTerm the self term.
     * @param contract the loop contract being applied.
     * @param heaps the heaps.
     * @param nextVariables the variables for the next loop iteration.
     * @param modifiableClauses the modified clauses.
     * @param freeModifiableClauses the free modified clauses.
     * @param services services.
     *        * @return the postconditions for the next loop iteration.
     */
    private static JTerm[] createPostconditionsNext(
            final JTerm selfTerm,
            final LoopContract contract,
            final List<LocationVariable> heaps,
            final LoopContract.Variables nextVariables,
            final Map<LocationVariable, JTerm> modifiableClauses,
            final Map<LocationVariable, JTerm> freeModifiableClauses,
            final Services services) {
        final JTerm nextPostcondition =
            new ConditionsAndClausesBuilder(contract, heaps, nextVariables, selfTerm, services)
                    .buildPostcondition();
        final JTerm nextFrameCondition =
            new ConditionsAndClausesBuilder(contract, heaps, nextVariables, selfTerm, services)
                    .buildFrameCondition(modifiableClauses, freeModifiableClauses);
        return new JTerm[] { nextPostcondition, nextFrameCondition };
    }

    /**
     *
     * @param heaps the heaps.
     * @param updatesBuilder an update builder.
     * @param instantiation the instantiation for the current rule application.
     * @param services services.
     * @return the update for the validity branch.
     */
    private static JTerm createContext(final List<LocationVariable> heaps,
            final UpdatesBuilder updatesBuilder, final Instantiation instantiation,
            final Services services) {
        return services.getTermBuilder().sequential(updatesBuilder.buildOuterRemembranceUpdate(),
            instantiation.update());
    }

    /**
     *
     * @param postconditions the postconditions.
     * @param anonOutHeaps the heaps used in the anonOut update.
     * @param localOutVariables all free program variables modified by the block.
     * @param conditionsAndClausesBuilder a ConditionsAndClausesBuilder.
     * @return preconditions for the usage branch.
     */
    private static JTerm[] createUsageAssumptions(final JTerm[] postconditions,
            final Map<LocationVariable, Function> anonOutHeaps,
            final ImmutableSet<LocationVariable> localOutVariables,
            final ConditionsAndClausesBuilder conditionsAndClausesBuilder) {
        final JTerm wellFormedAnonymisationHeapsCondition =
            conditionsAndClausesBuilder.buildWellFormedAnonymisationHeapsCondition(anonOutHeaps);
        final JTerm reachableOutCondition =
            conditionsAndClausesBuilder.buildReachableOutCondition(localOutVariables);
        final JTerm atMostOneFlagSetCondition =
            conditionsAndClausesBuilder.buildAtMostOneFlagSetCondition();
        return new JTerm[] { postconditions[0], wellFormedAnonymisationHeapsCondition,
            reachableOutCondition, atMostOneFlagSetCondition };
    }

    /**
     *
     * @param instantiation the instantiation.
     * @param heaps the heaps.
     * @param anonOutHeaps the heaps used in the anonOut update.
     * @param modifiableClauses the modifiable clauses.
     * @param updatesBuilder an update builder
     * @return the updates for the usage branch.
     */
    private static JTerm[] createUpdates(final Instantiation instantiation,
            final List<LocationVariable> heaps,
            final Map<LocationVariable, Function> anonOutHeaps,
            final Map<LocationVariable, JTerm> modifiableClauses,
            final UpdatesBuilder updatesBuilder) {
        final JTerm contextUpdate = instantiation.update();
        final JTerm remembranceUpdate = updatesBuilder.buildRemembranceUpdate(heaps);
        final JTerm anonymisationUpdate =
            updatesBuilder.buildAnonOutUpdate(anonOutHeaps, modifiableClauses);
        return new JTerm[] { contextUpdate, remembranceUpdate, anonymisationUpdate };
    }

    /**
     * @param goal the current goal.
     * @param selfTerm the self term.
     * @param contract the contract being applied.
     * @return the variables for both the current and the next loop iteration.
     */
    private static AuxiliaryContract.Variables[] createVars(final Goal goal, final JTerm selfTerm,
            final LoopContract contract) {
        final LoopContract.Variables variables =
            new VariablesCreatorAndRegistrar(goal, contract.getPlaceholderVariables())
                    .createAndRegister(selfTerm, true);

        final LoopContract.Variables nextVariables =
            new VariablesCreatorAndRegistrar(goal, variables)
                    .createAndRegisterCopies("_NEXT");
        return new LoopContract.Variables[] { variables, nextVariables };
    }

    @Override
    public JTerm getLastFocusTerm() {
        return lastFocusTerm;
    }

    @Override
    protected void setLastFocusTerm(JTerm lastFocusTerm) {
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
    public LoopContractInternalBuiltInRuleApp createApp(final PosInOccurrence occurrence,
            TermServices services) {
        return new LoopContractInternalBuiltInRuleApp(this, occurrence);
    }

    @Override
    public @NonNull ImmutableList<Goal> apply(final Goal goal,
            final RuleApp ruleApp) throws RuleAbortException {
        assert ruleApp instanceof LoopContractInternalBuiltInRuleApp;
        LoopContractInternalBuiltInRuleApp application =
            (LoopContractInternalBuiltInRuleApp) ruleApp;

        final Instantiation instantiation =
            instantiate((JTerm) application.posInOccurrence().subTerm(), goal);
        LoopContract contract = application.getContract();

        assert contract.isOnBlock() && contract.getBlock().equals(instantiation.statement())
                || !contract.isOnBlock() && contract.getLoop().equals(instantiation.statement());

        var services = goal.getOverlayServices();
        contract = contract.replaceEnhancedForVariables(contract.getBlock(), services);
        contract.setInstantiationSelf(instantiation.self());

        final List<LocationVariable> heaps = application.getHeapContext();
        final ImmutableSet<LocationVariable> localInVariables =
            MiscTools.getLocalIns(instantiation.statement(), services);
        final ImmutableSet<LocationVariable> localOutVariables =
            MiscTools.getLocalOuts(instantiation.statement(), services);
        final Map<LocationVariable, Function> anonOutHeaps =
            createAndRegisterAnonymisationVariables(heaps, contract, services);
        final LoopContract.Variables[] vars =
            createVars(goal, instantiation.self(), contract);

        final ConditionsAndClausesBuilder conditionsAndClausesBuilder =
            new ConditionsAndClausesBuilder(contract, heaps, vars[0], instantiation.self(),
                services);
        final Map<LocationVariable, JTerm> modifiableClauses =
            conditionsAndClausesBuilder.buildModifiableClauses();
        final Map<LocationVariable, JTerm> freeModifiableClauses =
            conditionsAndClausesBuilder.buildFreeModifiableClauses();
        final JTerm[] assumptions = createPreconditions(instantiation.self(), contract, heaps,
            localInVariables, conditionsAndClausesBuilder, services);
        final JTerm freePrecondition = conditionsAndClausesBuilder.buildFreePrecondition();
        final JTerm[] postconditions =
            createPostconditions(modifiableClauses, freeModifiableClauses,
                conditionsAndClausesBuilder);
        final JTerm freePostcondition = conditionsAndClausesBuilder.buildFreePostcondition();
        final JTerm[] usageAssumptions = createUsageAssumptions(postconditions, anonOutHeaps,
            localOutVariables, conditionsAndClausesBuilder);
        final JTerm decreasesCheck = conditionsAndClausesBuilder.buildDecreasesCheck();
        final JTerm[] postconditionsNext = createPostconditionsNext(
            instantiation.self(), contract,
            heaps, vars[1], modifiableClauses, freeModifiableClauses, services);
        final UpdatesBuilder updatesBuilder = new UpdatesBuilder(vars[0], services);
        final JTerm[] updates =
            createUpdates(instantiation, heaps, anonOutHeaps, modifiableClauses, updatesBuilder);
        final JTerm nextRemembranceUpdate =
            new UpdatesBuilder(vars[1], services).buildRemembranceUpdate(heaps);
        final JTerm context = createContext(heaps, updatesBuilder, instantiation, services);
        final GoalsConfigurator configurator =
            new GoalsConfigurator(application, new TermLabelState(), instantiation,
                contract.getLabels(), vars[0], application.posInOccurrence(), services, this);
        final ImmutableList<Goal> result = goal.split(3);

        configurator.setUpPreconditionGoal(result.tail().head(), updates[0], assumptions);
        configurator.setUpUsageGoal(result.head(), updates,
            ArrayUtil.add(usageAssumptions, freePostcondition));
        final LocationVariable exceptionParameter =
            createLocalVariable("e", vars[0].exception.getKeYJavaType(), services);
        configurator.setUpLoopValidityGoal(goal, contract, context, updates[1],
            nextRemembranceUpdate, anonOutHeaps, modifiableClauses,
            freeModifiableClauses,
            ArrayUtil.add(assumptions, freePrecondition), decreasesCheck, postconditions,
            postconditionsNext, exceptionParameter, vars[0].termify(instantiation.self()), vars[1]);

        return result;
    }
}
