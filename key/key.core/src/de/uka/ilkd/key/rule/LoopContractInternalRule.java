package de.uka.ilkd.key.rule;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSet;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.label.TermLabelState;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.BlockContractBuilders.ConditionsAndClausesBuilder;
import de.uka.ilkd.key.rule.BlockContractBuilders.GoalsConfigurator;
import de.uka.ilkd.key.rule.BlockContractBuilders.UpdatesBuilder;
import de.uka.ilkd.key.rule.BlockContractBuilders.VariablesCreatorAndRegistrar;
import de.uka.ilkd.key.speclang.LoopContract;
import de.uka.ilkd.key.util.MiscTools;

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
    private Term lastFocusTerm;

    /**
     * @see #getLastInstantiation()
     */
    private Instantiation lastInstantiation;

    private LoopContractInternalRule() {
    }

    /**
     *
     * @param selfTerm
     *            the self term.
     * @param contract
     *            the loop contract being applied.
     * @param heaps
     *            the heaps.
     * @param localInVariables
     *            all free program variables in the block.
     * @param conditionsAndClausesBuilder
     *            a ConditionsAndClausesBuilder.
     * @param services
     *            services.
     * @return the preconditions.
     */
    private static Term[] createPreconditions(final Term selfTerm, final LoopContract contract,
            final List<LocationVariable> heaps,
            final ImmutableSet<ProgramVariable> localInVariables,
            final ConditionsAndClausesBuilder conditionsAndClausesBuilder,
            final Services services) {
        final Term precondition = conditionsAndClausesBuilder.buildPrecondition();
        final Term wellFormedHeapsCondition
                = conditionsAndClausesBuilder.buildWellFormedHeapsCondition();
        final Term reachableInCondition
                = conditionsAndClausesBuilder.buildReachableInCondition(localInVariables);
        final Term selfConditions = conditionsAndClausesBuilder.buildSelfConditions(heaps,
                contract.getMethod(), contract.getKJT(), selfTerm, services);
        return new Term[] { precondition, wellFormedHeapsCondition, reachableInCondition,
            selfConditions };
    }

    /**
     *
     * @param localOutVariables
     *            all free program variables modified by the block.
     * @param anonymisationHeaps
     *            the anonymization heaps.
     * @param conditionsAndClausesBuilder
     *            a ConditionsAndClausesBuilder.
     * @return the postconditions for the current loop iteration.
     */
    private static Term[] createPostconditions(final Map<LocationVariable, Term> modifiesClauses,
            final ConditionsAndClausesBuilder conditionsAndClausesBuilder) {
        final Term postcondition = conditionsAndClausesBuilder.buildPostcondition();
        final Term frameCondition
                = conditionsAndClausesBuilder.buildFrameCondition(modifiesClauses);
        return new Term[] { postcondition, frameCondition };
    }

    /**
     *
     * @param selfTerm
     *            the self term.
     * @param contract
     *            the loop contract being applied.
     * @param heaps
     *            the heaps.
     * @param nextVariables
     *            the variables for the next loop iteration.
     * @param modifiesClauses
     *            the modified clauses
     * @param services
     *            services.
     * @return the postconditions for the next loop iteration.
     */
    private static Term[] createPostconditionsNext(final Term selfTerm, final LoopContract contract,
            final List<LocationVariable> heaps, final LoopContract.Variables nextVariables,
            final Map<LocationVariable, Term> modifiesClauses, final Services services) {
        final Term nextPostcondition = new ConditionsAndClausesBuilder(contract, heaps,
                nextVariables, selfTerm, services).buildPostcondition();
        final Term nextFrameCondition = new ConditionsAndClausesBuilder(contract, heaps,
                nextVariables, selfTerm, services).buildFrameCondition(modifiesClauses);
        return new Term[] { nextPostcondition, nextFrameCondition };
    }

    /**
     *
     * @param heaps
     *            the heaps.
     * @param updatesBuilder
     *            an update builder.
     * @param services
     *            services.
     * @return the update for the validity branch.
     */
    private static Term createContext(final List<LocationVariable> heaps,
            final UpdatesBuilder updatesBuilder, final Services services) {
        final Term outerRemembranceUpdate = updatesBuilder.buildOuterRemembranceUpdate();
        Map<LocationVariable, Function> anonInHeaps
                = new LinkedHashMap<LocationVariable, Function>(40);
        final TermBuilder tb = services.getTermBuilder();

        for (LocationVariable heap : heaps) {
            final String anonymisationName
                    = tb.newName(BlockContractBuilders.ANON_IN_PREFIX + heap.name());
            final Function anonymisationFunction
                    = new Function(new Name(anonymisationName), heap.sort(), true);
            services.getNamespaces().functions().addSafely(anonymisationFunction);
            anonInHeaps.put(heap, anonymisationFunction);
        }
        final Term anonInUpdate = updatesBuilder.buildAnonInUpdate(anonInHeaps);
        return tb.sequential(outerRemembranceUpdate, anonInUpdate);
    }

    /**
     *
     * @param postconditions
     *            the postconditions.
     * @param anonOutHeaps
     *            the heaps used in the anonOut update.
     * @param localOutVariables
     *            all free program variables modified by the block.
     * @param conditionsAndClausesBuilder
     *            a ConditionsAndClausesBuilder.
     * @return preconditions for the usage branch.
     */
    private static Term[] createUsageAssumptions(final Term[] postconditions,
            final Map<LocationVariable, Function> anonOutHeaps,
            final ImmutableSet<ProgramVariable> localOutVariables,
            final ConditionsAndClausesBuilder conditionsAndClausesBuilder) {
        final Term wellFormedAnonymisationHeapsCondition = conditionsAndClausesBuilder
                .buildWellFormedAnonymisationHeapsCondition(anonOutHeaps);
        final Term reachableOutCondition
                = conditionsAndClausesBuilder.buildReachableOutCondition(localOutVariables);
        final Term atMostOneFlagSetCondition
                = conditionsAndClausesBuilder.buildAtMostOneFlagSetCondition();
        return new Term[] { postconditions[0], wellFormedAnonymisationHeapsCondition,
            reachableOutCondition, atMostOneFlagSetCondition };
    }

    /**
     *
     * @param instantiation
     *            the instantiation.
     * @param heaps
     *            the heaps.
     * @param anonOutHeaps
     *            the heaps used in the anonOut update.
     * @param modifiesClauses
     *            the modifies clauses.
     * @param updatesBuilder
     *            an update builder
     * @return the updates for the usage branch.
     */
    private static Term[] createUpdates(final Instantiation instantiation,
            final List<LocationVariable> heaps, final Map<LocationVariable, Function> anonOutHeaps,
            final Map<LocationVariable, Term> modifiesClauses,
            final UpdatesBuilder updatesBuilder) {
        final Term contextUpdate = instantiation.update;
        final Term remembranceUpdate = updatesBuilder.buildRemembranceUpdate(heaps);
        final Term anonymisationUpdate
                = updatesBuilder.buildAnonOutUpdate(anonOutHeaps, modifiesClauses);
        return new Term[] { contextUpdate, remembranceUpdate, anonymisationUpdate };
    }

    /**
     *
     * @param goal
     *            the current goal.
     * @param selfTerm
     *            the self term.
     * @param contract
     *            the contract being applied.
     * @param services
     *            services.
     * @return the variables for both the current and the next loop iteration.
     */
    private static LoopContract.Variables[] createVars(final Goal goal, final Term selfTerm,
            final LoopContract contract, final Services services) {
        final LoopContract.Variables variables = new VariablesCreatorAndRegistrar(goal,
                contract.getPlaceholderVariables(), services).createAndRegister(selfTerm, true);

        final LoopContract.Variables nextVariables
                = new VariablesCreatorAndRegistrar(goal, variables, services)
                        .createAndRegisterCopies("_NEXT");
        return new LoopContract.Variables[] { variables, nextVariables };
    }

    /**
     *
     * @param goal
     *            the current goal.
     * @param result
     *            the next goals.
     * @param contract
     *            the contract being applied.
     * @param instantiation
     *            the instantiation.
     * @param anonOutHeaps
     *            the heaps used in the anonOut update.
     * @param vars
     *            the variables for both the current and the next loop iteration.
     * @param modifiesClauses
     *            the modifies clauses.
     * @param assumptions
     *            the preconditions for the validity branch.
     * @param usageAssumptions
     *            the preconditions for the usage branch.
     * @param decreasesCheck
     *            the decreases check.
     * @param postconditions
     *            the postconditions for the current loop iteration.
     * @param postconditionsNext
     *            the postconditions for the next loop iteration.
     * @param updates
     *            the updates for the usage branch.
     * @param nextRemembranceUpdate
     *            the remembrance update for the next loop iteration.
     * @param context
     *            the update for the validity branch.
     * @param configurator
     *            a configurator.
     * @param services
     *            services.
     */
    private static void setUpGoals(final Goal goal, final ImmutableList<Goal> result,
            final LoopContract contract, final Instantiation instantiation,
            final Map<LocationVariable, Function> anonOutHeaps, final LoopContract.Variables[] vars,
            final Map<LocationVariable, Term> modifiesClauses, final Term[] assumptions,
            final Term[] usageAssumptions, final Term decreasesCheck, final Term[] postconditions,
            final Term[] postconditionsNext, final Term[] updates, final Term nextRemembranceUpdate,
            final Term context, final GoalsConfigurator configurator, final Services services) {
        configurator.setUpPreconditionGoal(result.tail().head(), updates[0], assumptions);
        configurator.setUpUsageGoal(result.head(), updates, usageAssumptions);
        final ProgramVariable exceptionParameter
                = createLocalVariable("e", vars[0].exception.getKeYJavaType(), services);
        configurator.setUpLoopValidityGoal(goal, contract, context, updates[1],
                nextRemembranceUpdate, anonOutHeaps, modifiesClauses, assumptions, decreasesCheck,
                postconditions, postconditionsNext, exceptionParameter,
                vars[0].termify(instantiation.self), vars[1]);
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
    public LoopContractInternalBuiltInRuleApp createApp(final PosInOccurrence occurrence,
            TermServices services) {
        return new LoopContractInternalBuiltInRuleApp(this, occurrence);
    }

    @Override
    public ImmutableList<Goal> apply(final Goal goal, final Services services,
            final RuleApp ruleApp) throws RuleAbortException {
        assert ruleApp instanceof LoopContractInternalBuiltInRuleApp;
        LoopContractInternalBuiltInRuleApp application
                = (LoopContractInternalBuiltInRuleApp) ruleApp;

        final Instantiation instantiation
                = instantiate(application.posInOccurrence().subTerm(), goal, services);
        final LoopContract contract = application.getContract();
        contract.setInstantiationSelf(instantiation.self);
        assert contract.getBlock().equals(instantiation.block);

        final List<LocationVariable> heaps = application.getHeapContext();
        final ImmutableSet<ProgramVariable> localInVariables
                = MiscTools.getLocalIns(instantiation.block, services);
        final ImmutableSet<ProgramVariable> localOutVariables
                = MiscTools.getLocalOuts(instantiation.block, services);
        final Map<LocationVariable, Function> anonOutHeaps
                = createAndRegisterAnonymisationVariables(heaps, contract, services);
        final LoopContract.Variables[] vars
                = createVars(goal, instantiation.self, contract, services);

        final ConditionsAndClausesBuilder conditionsAndClausesBuilder
                = new ConditionsAndClausesBuilder(contract, heaps, vars[0], instantiation.self,
                        services);
        final Map<LocationVariable, Term> modifiesClauses
                = conditionsAndClausesBuilder.buildModifiesClauses();
        final Term[] assumptions = createPreconditions(instantiation.self, contract, heaps,
                localInVariables, conditionsAndClausesBuilder, services);
        final Term[] postconditions
                = createPostconditions(modifiesClauses, conditionsAndClausesBuilder);
        final Term[] usageAssumptions = createUsageAssumptions(postconditions, anonOutHeaps,
                localOutVariables, conditionsAndClausesBuilder);
        final Term decreasesCheck = conditionsAndClausesBuilder.buildDecreasesCheck();
        final Term[] postconditionsNext = createPostconditionsNext(instantiation.self, contract,
                heaps, vars[1], modifiesClauses, services);
        final UpdatesBuilder updatesBuilder = new UpdatesBuilder(vars[0], services);
        final Term[] updates = createUpdates(instantiation, heaps, anonOutHeaps, modifiesClauses,
                updatesBuilder);
        final Term nextRemembranceUpdate
                = new UpdatesBuilder(vars[1], services).buildRemembranceUpdate(heaps);
        final Term context = createContext(heaps, updatesBuilder, services);
        final GoalsConfigurator configurator = new GoalsConfigurator(application,
                new TermLabelState(), instantiation, contract.getLabels(), vars[0],
                application.posInOccurrence(), services, this);
        final ImmutableList<Goal> result = goal.split(3);
        setUpGoals(goal, result, contract, instantiation, anonOutHeaps, vars, modifiesClauses,
                assumptions, usageAssumptions, decreasesCheck, postconditions, postconditionsNext,
                updates, nextRemembranceUpdate, context, configurator, services);
        return result;
    }
}
