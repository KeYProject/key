/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.rule;

import java.util.List;
import java.util.Map;
import java.util.Objects;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.label.TermLabelState;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.init.FunctionalBlockContractPO;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.mgt.ComplexRuleJustificationBySpec;
import de.uka.ilkd.key.proof.mgt.RuleJustificationBySpec;
import de.uka.ilkd.key.proof.rules.ComplexJustificationable;
import de.uka.ilkd.key.rule.AuxiliaryContractBuilders.ConditionsAndClausesBuilder;
import de.uka.ilkd.key.rule.AuxiliaryContractBuilders.GoalsConfigurator;
import de.uka.ilkd.key.rule.AuxiliaryContractBuilders.UpdatesBuilder;
import de.uka.ilkd.key.rule.AuxiliaryContractBuilders.VariablesCreatorAndRegistrar;
import de.uka.ilkd.key.speclang.BlockContract;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.util.MiscTools;

import org.key_project.logic.Name;
import org.key_project.logic.op.Function;
import org.key_project.prover.rules.RuleAbortException;
import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSet;
import org.key_project.util.java.ArrayUtil;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

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
@NullMarked
public final class BlockContractExternalRule extends AbstractBlockContractRule
        implements ComplexJustificationable {

    /**
     * The only instance of this class.
     */
    public static final BlockContractExternalRule INSTANCE = new BlockContractExternalRule();

    /**
     * This rule's name.
     */
    private static final Name NAME = new Name("Block Contract (External)");

    /**
     * Single-entry memo to avoid recomputing the instantiation between the applicability check and
     * the application of the same focus term. Thread-local because this rule's {@link #INSTANCE} is
     * a shared singleton and {@code instantiate} is reached from the applicability check off the
     * parallel prover's commit lock: a plain field pair raced across concurrent workers and could
     * hand one worker another goal's instantiation. Confined to the worker thread it preserves the
     * memo (applicability and apply run on the same worker).
     *
     * @see #getLastFocusTerm()
     */
    private final ThreadLocal<JTerm> lastFocusTerm = new ThreadLocal<>();

    /**
     * @see #getLastInstantiation()
     */
    private final ThreadLocal<Instantiation> lastInstantiation = new ThreadLocal<>();

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
    private static JTerm[] createPreconditions(final Instantiation instantiation,
            final BlockContract contract, final List<LocationVariable> heaps,
            final ImmutableSet<LocationVariable> localInVariables,
            final ConditionsAndClausesBuilder conditionsAndClausesBuilder,
            final Services services) {
        final JTerm precondition = conditionsAndClausesBuilder.buildPrecondition();
        final JTerm wellFormedHeapsCondition =
            conditionsAndClausesBuilder.buildWellFormedHeapsCondition();
        final JTerm reachableInCondition =
            conditionsAndClausesBuilder.buildReachableInCondition(localInVariables);
        final JTerm selfConditions = conditionsAndClausesBuilder.buildSelfConditions(heaps,
            contract.getMethod(), contract.getKJT(), instantiation.self(), services);
        return new JTerm[] { precondition, wellFormedHeapsCondition, reachableInCondition,
            selfConditions };
    }

    /**
     *
     * @param localOutVariables all free program variables modified by the block.
     * @param anonymisationHeaps the anonymization heaps.
     * @param conditionsAndClausesBuilder a ConditionsAndClausesBuilder.
     * @return the postconditions.
     */
    private static JTerm[] createAssumptions(final ImmutableSet<LocationVariable> localOutVariables,
            final Map<LocationVariable, Function> anonymisationHeaps,
            final ConditionsAndClausesBuilder conditionsAndClausesBuilder) {
        final JTerm postcondition = conditionsAndClausesBuilder.buildPostcondition();
        final JTerm wellFormedAnonymisationHeapsCondition = conditionsAndClausesBuilder
                .buildWellFormedAnonymisationHeapsCondition(anonymisationHeaps);
        final JTerm reachableOutCondition =
            conditionsAndClausesBuilder.buildReachableOutCondition(localOutVariables);
        final JTerm atMostOneFlagSetCondition =
            conditionsAndClausesBuilder.buildAtMostOneFlagSetCondition();
        return new JTerm[] { postcondition, wellFormedAnonymisationHeapsCondition,
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
    private static JTerm[] createUpdates(final JTerm contextUpdate,
            final List<LocationVariable> heaps,
            final Map<LocationVariable, Function> anonymisationHeaps,
            final BlockContract.Variables variables,
            final ConditionsAndClausesBuilder conditionsAndClausesBuilder,
            final Services services) {
        final Map<LocationVariable, JTerm> modifiableClauses =
            conditionsAndClausesBuilder.buildModifiableClauses();
        final UpdatesBuilder updatesBuilder = new UpdatesBuilder(variables, services);
        final JTerm remembranceUpdate = updatesBuilder.buildRemembranceUpdate(heaps);
        final JTerm anonymisationUpdate =
            updatesBuilder.buildAnonOutUpdate(anonymisationHeaps, modifiableClauses);
        final JTerm[] updates = { contextUpdate, remembranceUpdate, anonymisationUpdate };
        return updates;
    }

    @Override
    public @Nullable JTerm getLastFocusTerm() {
        return lastFocusTerm.get();
    }

    @Override
    protected void setLastFocusTerm(JTerm lastFocusTerm) {
        this.lastFocusTerm.set(lastFocusTerm);
    }

    @Override
    public @Nullable Instantiation getLastInstantiation() {
        return lastInstantiation.get();
    }

    @Override
    public Name name() {
        return NAME;
    }

    @Override
    protected void setLastInstantiation(@Nullable Instantiation lastInstantiation) {
        this.lastInstantiation.set(lastInstantiation);
    }

    @Override
    public IBuiltInRuleApp createApp(@Nullable PosInOccurrence pos, TermServices services) {
        return new BlockContractExternalBuiltInRuleApp<>(this,
            Objects.requireNonNull(pos, "rule application needs a position"));
    }

    /// Not applicable for information, but this is excluded by using the right profile.
    // The self term is absent for static methods and {@code setInstantiationSelf} (in the
    // out-of-scope speclang package) stores it as-is; the conditions builders null-check it.
    @SuppressWarnings("NullAway")
    @Override
    public ImmutableList<Goal> apply(final Goal goal, final RuleApp ruleApp)
            throws RuleAbortException {
        var application = (BlockContractExternalBuiltInRuleApp<?>) ruleApp;

        final PosInOccurrence pio = Objects.requireNonNull(application.posInOccurrence(),
            "block contract app requires an occurrence");
        final Instantiation instantiation = Objects.requireNonNull(
            instantiate((JTerm) pio.subTerm(), goal), "no instantiation for block contract");
        final BlockContract contract = Objects.requireNonNull(application.getContract(),
            "no block contract set for rule application");
        contract.setInstantiationSelf(instantiation.self());
        assert contract.getBlock().equals(instantiation.statement());

        final var services = goal.getOverlayServices();
        final List<LocationVariable> heaps = Objects.requireNonNull(application.getHeapContext(),
            "no heap context for rule application");
        final ImmutableSet<LocationVariable> localInVariables =
            MiscTools.getLocalIns(instantiation.statement(), services);
        final ImmutableSet<LocationVariable> localOutVariables =
            MiscTools.getLocalOuts(instantiation.statement(), services);
        final Map<LocationVariable, Function> anonymisationHeaps =
            createAndRegisterAnonymisationVariables(heaps, contract, services);
        final BlockContract.Variables variables =
            new VariablesCreatorAndRegistrar(goal, contract.getPlaceholderVariables())
                    .createAndRegister(instantiation.self(), true);

        final ConditionsAndClausesBuilder conditionsAndClausesBuilder =
            new ConditionsAndClausesBuilder(contract, heaps, variables, instantiation.self(),
                services);
        final JTerm[] preconditions = createPreconditions(instantiation, contract, heaps,
            localInVariables, conditionsAndClausesBuilder, services);
        final JTerm[] assumptions =
            createAssumptions(localOutVariables, anonymisationHeaps, conditionsAndClausesBuilder);
        final JTerm freePostcondition = conditionsAndClausesBuilder.buildFreePostcondition();
        final JTerm[] updates = createUpdates(instantiation.update(), heaps, anonymisationHeaps,
            variables, conditionsAndClausesBuilder, services);

        final ImmutableList<Goal> result = goal.split(2);
        final GoalsConfigurator configurator =
            new GoalsConfigurator(application, new TermLabelState(), instantiation,
                contract.getLabels(), variables, application.posInOccurrence(), services, this);
        configurator.setUpPreconditionGoal(result.tail().head(), updates[0], preconditions);
        configurator.setUpUsageGoal(result.head(), updates,
            ArrayUtil.add(assumptions, freePostcondition));

        final InitConfig initConfig = Objects.requireNonNull(goal.proof().getInitConfig(),
            "no initial configuration");
        final ComplexRuleJustificationBySpec cjust = Objects.requireNonNull(
            (ComplexRuleJustificationBySpec) initConfig.getJustifInfo().getJustification(this),
            "no rule justification for rule application");
        for (Contract c : contract.getFunctionalContracts()) {
            cjust.add(application, new RuleJustificationBySpec(c));
        }

        return result;
    }
}
