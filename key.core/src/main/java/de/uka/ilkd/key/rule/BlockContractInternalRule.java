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
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.Transformer;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.AuxiliaryContractBuilders.ConditionsAndClausesBuilder;
import de.uka.ilkd.key.rule.AuxiliaryContractBuilders.GoalsConfigurator;
import de.uka.ilkd.key.rule.AuxiliaryContractBuilders.UpdatesBuilder;
import de.uka.ilkd.key.rule.AuxiliaryContractBuilders.VariablesCreatorAndRegistrar;
import de.uka.ilkd.key.speclang.BlockContract;
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
 * Rule for the application of {@link BlockContract}s.
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
 * @see BlockContractInternalBuiltInRuleApp
 *
 * @author wacker, lanzinger
 */
public class BlockContractInternalRule extends AbstractBlockContractRule {

    /**
     * The only instance of this class.
     */
    public static final BlockContractInternalRule INSTANCE = new BlockContractInternalRule();

    /**
     * This rule's name.
     */
    private static final Name NAME = new Name("Block Contract (Internal)");

    /**
     * @see #getLastFocusTerm()
     */
    private JTerm lastFocusTerm;

    /**
     * @see #getLastInstantiation()
     */
    private Instantiation lastInstantiation;

    protected BlockContractInternalRule() {
    }

    /**
     *
     * @param contract the contract being applied.
     * @param self the self term.
     * @param heaps the heaps.
     * @param localInVariables all free program variables in the block.
     * @param conditionsAndClausesBuilder a ConditionsAndClausesBuilder.
     * @param services services.
     * @return the preconditions.
     */
    private static JTerm[] createPreconditions(final BlockContract contract, final JTerm self,
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
            contract.getMethod(), contract.getKJT(), self, services);
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
     * @param modifiableClauses the modified clauses.
     * @param services services.
     * @return the updates.
     */
    private static JTerm[] createUpdates(final JTerm contextUpdate,
            final List<LocationVariable> heaps,
            final Map<LocationVariable, Function> anonymisationHeaps,
            final BlockContract.Variables variables,
            final Map<LocationVariable, JTerm> modifiableClauses, final Services services) {
        final UpdatesBuilder updatesBuilder = new UpdatesBuilder(variables, services);
        final JTerm remembranceUpdate = updatesBuilder.buildRemembranceUpdate(heaps);
        final JTerm anonymisationUpdate =
            updatesBuilder.buildAnonOutUpdate(anonymisationHeaps, modifiableClauses);
        return new JTerm[] { contextUpdate, remembranceUpdate, anonymisationUpdate };
    }

    /**
     *
     * @param goal the current goal.
     * @param contract the contract being applied.
     * @param heaps the heaps.
     * @param localInVariables all free program variables in the block.
     * @param anonymisationHeaps the anonymization heaps.
     * @param contextUpdate the context update.
     * @param remembranceUpdate the remembrance update.
     * @param localOutVariables all free program variables modified by the block.
     * @param configurator a configurator.
     * @param services services.
     * @return a list containing the new goals.
     */
    protected ImmutableList<Goal> splitIntoGoals(final Goal goal, final BlockContract contract,
            final List<LocationVariable> heaps,
            final ImmutableSet<LocationVariable> localInVariables,
            final Map<LocationVariable, Function> anonymisationHeaps,
            final JTerm contextUpdate,
            final JTerm remembranceUpdate, final ImmutableSet<LocationVariable> localOutVariables,
            final GoalsConfigurator configurator, final Services services) {
        return goal.split(3);
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
    public BlockContractInternalBuiltInRuleApp<BlockContractInternalRule> createApp(
            final PosInOccurrence occurrence, TermServices services) {
        return new BlockContractInternalBuiltInRuleApp<>(this, occurrence);
    }

    @Override
    public @NonNull ImmutableList<Goal> apply(final Goal goal, final RuleApp ruleApp)
            throws RuleAbortException {
        assert ruleApp instanceof BlockContractInternalBuiltInRuleApp<?>;
        var application = (BlockContractInternalBuiltInRuleApp<?>) ruleApp;

        final Instantiation instantiation =
            instantiate((JTerm) application.posInOccurrence().subTerm(), goal);
        final BlockContract contract = application.getContract();
        contract.setInstantiationSelf(instantiation.self());
        assert contract.getBlock().equals(instantiation.statement());
        final JTerm contextUpdate = instantiation.update();

        final var services = goal.getOverlayServices();
        final List<LocationVariable> heaps = application.getHeapContext();
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
        final JTerm[] preconditions = createPreconditions(contract, instantiation.self(), heaps,
            localInVariables, conditionsAndClausesBuilder, services);
        final JTerm freePrecondition = conditionsAndClausesBuilder.buildFreePrecondition();
        final Map<LocationVariable, JTerm> modifiableClauses =
            conditionsAndClausesBuilder.buildModifiableClauses();
        final Map<LocationVariable, JTerm> freeModifiableClauses =
            conditionsAndClausesBuilder.buildFreeModifiableClauses();
        final JTerm frameCondition =
            conditionsAndClausesBuilder.buildFrameCondition(
                modifiableClauses, freeModifiableClauses);
        final JTerm[] assumptions =
            createAssumptions(localOutVariables, anonymisationHeaps, conditionsAndClausesBuilder);
        final JTerm freePostcondition = conditionsAndClausesBuilder.buildFreePostcondition();
        final JTerm[] updates = createUpdates(instantiation.update(), heaps, anonymisationHeaps,
            variables, modifiableClauses, services);

        final GoalsConfigurator configurator =
            new GoalsConfigurator(application, new TermLabelState(), instantiation,
                contract.getLabels(), variables, application.posInOccurrence(), services, this);
        final ImmutableList<Goal> result = splitIntoGoals(goal, contract, heaps, localInVariables,
            anonymisationHeaps, updates[0], updates[1], localOutVariables, configurator, services);

        configurator.setUpPreconditionGoal(result.tail().head(), contextUpdate, preconditions);
        configurator.setUpUsageGoal(result.head(), updates,
            ArrayUtil.add(assumptions, freePostcondition));

        final boolean isInfFlow = false;// InfFlowCheckInfo.isInfFlow(goal);
        setUpValidityGoal(result, contract, application, instantiation, heaps,
            anonymisationHeaps, localInVariables, localOutVariables, variables,
            ArrayUtil.add(preconditions, freePrecondition), assumptions, frameCondition, updates,
            configurator, conditionsAndClausesBuilder, services);
        return result;
    }

    @Override
    public boolean isApplicable(Goal goal,
            PosInOccurrence occurrence) {
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

        // If we are using internal rules, we can apply the respective loop contract directly,
        // without first applying this block contract.
        return !contracts.isEmpty() && contracts.stream().allMatch(c -> c.toLoopContract() == null);
    }

    /**
     * Sets up the validity goal as the first goal in the list.
     *
     * @param result the new goals.
     * @param contract the block contract being applied.
     * @param application the rule application.
     * @param instantiation the instantiation.
     * @param heaps the heaps.
     * @param anonymisationHeaps the anonymization heaps.
     * @param localInVariables all free program variables in the block.
     * @param localOutVariables all free program variables modified by the block.
     * @param variables the variables.
     * @param preconditions the preconditions.
     * @param assumptions the postconditions.
     * @param frameCondition the framing condition.
     * @param updates the updates.
     * @param configurator a Configurator.
     * @param conditionsAndClausesBuilder a ConditionsAndClausesBuilder
     * @param services services.
     */
    protected void setUpValidityGoal(final ImmutableList<Goal> result,
            final BlockContract contract, final BlockContractInternalBuiltInRuleApp<?> application,
            final Instantiation instantiation, final List<LocationVariable> heaps,
            final Map<LocationVariable, Function> anonymisationHeaps,
            final ImmutableSet<LocationVariable> localInVariables,
            final ImmutableSet<LocationVariable> localOutVariables,
            final BlockContract.Variables variables, final JTerm[] preconditions,
            final JTerm[] assumptions, final JTerm frameCondition, final JTerm[] updates,
            final GoalsConfigurator configurator,
            final ConditionsAndClausesBuilder conditionsAndClausesBuilder,
            final Services services) {
        Goal validityGoal = result.tail().tail().head();
        final ProgramVariable exceptionParameter =
            createLocalVariable("e", variables.exception.getKeYJavaType(), services);
        configurator.setUpValidityGoal(validityGoal, new JTerm[] { updates[0], updates[1] },
            preconditions, new JTerm[] { assumptions[0], frameCondition }, exceptionParameter,
            conditionsAndClausesBuilder.terms);
    }
}
