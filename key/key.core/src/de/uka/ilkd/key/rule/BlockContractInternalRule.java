// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.rule;

import java.util.List;
import java.util.Map;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSet;

import de.uka.ilkd.key.informationflow.proof.InfFlowCheckInfo;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
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
import de.uka.ilkd.key.speclang.BlockContract;
import de.uka.ilkd.key.speclang.WellDefinednessCheck;
import de.uka.ilkd.key.util.MiscTools;

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
public final class BlockContractInternalRule extends AbstractBlockContractRule {

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
    private Term lastFocusTerm;

    /**
     * @see #getLastInstantiation()
     */
    private Instantiation lastInstantiation;

    private BlockContractInternalRule() {
    }

    /**
     *
     * @param contract
     *            the contract being applied.
     * @param self
     *            the self term.
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
    private static Term[] createPreconditions(final BlockContract contract, final Term self,
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
                contract.getMethod(), contract.getKJT(), self, services);
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
     * @return the postconditions.
     */
    private static Term[] createAssumptions(final ImmutableSet<ProgramVariable> localOutVariables,
            final Map<LocationVariable, Function> anonymisationHeaps,
            final ConditionsAndClausesBuilder conditionsAndClausesBuilder) {
        final Term postcondition = conditionsAndClausesBuilder.buildPostcondition();
        final Term wellFormedAnonymisationHeapsCondition = conditionsAndClausesBuilder
                .buildWellFormedAnonymisationHeapsCondition(anonymisationHeaps);
        final Term reachableOutCondition
                = conditionsAndClausesBuilder.buildReachableOutCondition(localOutVariables);
        final Term atMostOneFlagSetCondition
                = conditionsAndClausesBuilder.buildAtMostOneFlagSetCondition();
        return new Term[] { postcondition, wellFormedAnonymisationHeapsCondition,
            reachableOutCondition, atMostOneFlagSetCondition };
    }

    /**
     *
     * @param contextUpdate
     *            the context update.
     * @param heaps
     *            the heaps.
     * @param anonymisationHeaps
     *            the anonymization heaps.
     * @param variables
     *            the variables.
     * @param modifiesClauses
     *            the modified clauses.
     * @param services
     *            services.
     * @return the updates.
     */
    private static Term[] createUpdates(final Term contextUpdate,
            final List<LocationVariable> heaps,
            final Map<LocationVariable, Function> anonymisationHeaps,
            final BlockContract.Variables variables,
            final Map<LocationVariable, Term> modifiesClauses, final Services services) {
        final UpdatesBuilder updatesBuilder = new UpdatesBuilder(variables, services);
        final Term remembranceUpdate = updatesBuilder.buildRemembranceUpdate(heaps);
        final Term anonymisationUpdate
                = updatesBuilder.buildAnonOutUpdate(anonymisationHeaps, modifiesClauses);
        return new Term[] { contextUpdate, remembranceUpdate, anonymisationUpdate };
    }

    /**
     *
     * @param goal
     *            the current goal.
     * @param contract
     *            the contract being applied.
     * @param heaps
     *            the heaps.
     * @param localInVariables
     *            all free program variables in the block.
     * @param anonymisationHeaps
     *            the anonymization heaps.
     * @param contextUpdate
     *            the context update.
     * @param remembranceUpdate
     *            the remembrance update.
     * @param localOutVariables
     *            all free program variables modified by the block.
     * @param configurator
     *            a configurator.
     * @param services
     *            services.
     * @return a list containing the new goals.
     */
    private static ImmutableList<Goal> splitIntoGoals(final Goal goal, final BlockContract contract,
            final List<LocationVariable> heaps,
            final ImmutableSet<ProgramVariable> localInVariables,
            final Map<LocationVariable, Function> anonymisationHeaps, final Term contextUpdate,
            final Term remembranceUpdate, final ImmutableSet<ProgramVariable> localOutVariables,
            final GoalsConfigurator configurator, final Services services) {
        final ImmutableList<Goal> result;
        final LocationVariable heap = heaps.get(0);
        if (WellDefinednessCheck.isOn()) {
            result = goal.split(4);
            final Term localAnonUpdate = createLocalAnonUpdate(localOutVariables, services);
            final Term wdUpdate
                    = services.getTermBuilder().parallel(contextUpdate, remembranceUpdate);
            configurator.setUpWdGoal(result.tail().tail().tail().head(), contract, wdUpdate,
                    localAnonUpdate, heap, anonymisationHeaps.get(heap), localInVariables);
        } else {
            result = goal.split(3);
        }
        return result;
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
    public BlockContractInternalBuiltInRuleApp createApp(final PosInOccurrence occurrence,
            TermServices services) {
        return new BlockContractInternalBuiltInRuleApp(this, occurrence);
    }

    @Override
    public ImmutableList<Goal> apply(final Goal goal, final Services services,
            final RuleApp ruleApp) throws RuleAbortException {
        assert ruleApp instanceof BlockContractInternalBuiltInRuleApp;
        BlockContractInternalBuiltInRuleApp application
                = (BlockContractInternalBuiltInRuleApp) ruleApp;

        final Instantiation instantiation
                = instantiate(application.posInOccurrence().subTerm(), goal, services);
        final BlockContract contract = application.getContract();
        contract.setInstantiationSelf(instantiation.self);
        assert contract.getBlock().equals(instantiation.block);
        final Term contextUpdate = instantiation.update;

        final List<LocationVariable> heaps = application.getHeapContext();
        final ImmutableSet<ProgramVariable> localInVariables
                = MiscTools.getLocalIns(instantiation.block, services);
        final ImmutableSet<ProgramVariable> localOutVariables
                = MiscTools.getLocalOuts(instantiation.block, services);
        final Map<LocationVariable, Function> anonymisationHeaps
                = createAndRegisterAnonymisationVariables(heaps, contract, services);
        final BlockContract.Variables variables
                = new VariablesCreatorAndRegistrar(goal, contract.getPlaceholderVariables(),
                        services).createAndRegister(instantiation.self, true);

        final ConditionsAndClausesBuilder conditionsAndClausesBuilder
                = new ConditionsAndClausesBuilder(contract, heaps, variables, instantiation.self,
                        services);
        final Term[] preconditions = createPreconditions(contract, instantiation.self, heaps,
                localInVariables, conditionsAndClausesBuilder, services);
        final Map<LocationVariable, Term> modifiesClauses
                = conditionsAndClausesBuilder.buildModifiesClauses();
        final Term frameCondition
                = conditionsAndClausesBuilder.buildFrameCondition(modifiesClauses);
        final Term[] assumptions = createAssumptions(localOutVariables, anonymisationHeaps,
                conditionsAndClausesBuilder);
        final Term[] updates = createUpdates(instantiation.update, heaps, anonymisationHeaps,
                variables, modifiesClauses, services);

        final GoalsConfigurator configurator = new GoalsConfigurator(application,
                new TermLabelState(), instantiation, contract.getLabels(), variables,
                application.posInOccurrence(), services, this);
        final ImmutableList<Goal> result
                = splitIntoGoals(goal, contract, heaps, localInVariables, anonymisationHeaps,
                        updates[0], updates[1], localOutVariables, configurator, services);

        configurator.setUpPreconditionGoal(result.tail().head(), contextUpdate, preconditions);
        configurator.setUpUsageGoal(result.head(), updates, assumptions);

        final boolean isInfFlow = InfFlowCheckInfo.isInfFlow(goal);
        setUpValidityGoal(result, isInfFlow, contract, application, instantiation, heaps,
                anonymisationHeaps, localInVariables, localOutVariables, variables, preconditions,
                assumptions, frameCondition, updates, configurator, conditionsAndClausesBuilder,
                services);
        return result;
    }

    /**
     * Sets up the validity goal as the first goal in the list.
     *
     * @param result
     *            the new goals.
     * @param isInfFlow
     *            whether or not this is an information flow proof.
     * @param contract
     *            the block contract being applied.
     * @param application
     *            the rule application.
     * @param instantiation
     *            the instantiation.
     * @param heaps
     *            the heaps.
     * @param anonymisationHeaps
     *            the anonymization heaps.
     * @param localInVariables
     *            all free program variables in the block.
     * @param localOutVariables
     *            all free program variables modified by the block.
     * @param variables
     *            the variables.
     * @param preconditions
     *            the preconditions.
     * @param assumptions
     *            the postconditions.
     * @param frameCondition
     *            the framing condition.
     * @param updates
     *            the updates.
     * @param configurator
     *            a Configurator.
     * @param conditionsAndClausesBuilder
     *            a ConditionsAndClausesBuilder
     * @param services
     *            services.
     */
    private void setUpValidityGoal(final ImmutableList<Goal> result, final boolean isInfFlow,
            final BlockContract contract, final BlockContractInternalBuiltInRuleApp application,
            final Instantiation instantiation, final List<LocationVariable> heaps,
            final Map<LocationVariable, Function> anonymisationHeaps,
            final ImmutableSet<ProgramVariable> localInVariables,
            final ImmutableSet<ProgramVariable> localOutVariables,
            final BlockContract.Variables variables, final Term[] preconditions,
            final Term[] assumptions, final Term frameCondition, final Term[] updates,
            final GoalsConfigurator configurator,
            final ConditionsAndClausesBuilder conditionsAndClausesBuilder,
            final Services services) {
        Goal validityGoal = result.tail().tail().head();
        final ProgramVariable exceptionParameter
                = createLocalVariable("e", variables.exception.getKeYJavaType(), services);
        if (!isInfFlow) {
            configurator.setUpValidityGoal(validityGoal, new Term[] { updates[0], updates[1] },
                    preconditions, new Term[] { assumptions[0], frameCondition },
                    exceptionParameter, conditionsAndClausesBuilder.terms);
        } else {
            validityGoal.setBranchLabel("Information Flow Validity");

            // clear goal
            validityGoal.node().setSequent(Sequent.EMPTY_SEQUENT);
            validityGoal.clearAndDetachRuleAppIndex();
            final TermBuilder tb = services.getTermBuilder();

            if (contract.hasModifiesClause(heaps.get(0)) && contract.hasInfFlowSpecs()) {
                // set up information flow validity goal
                InfFlowValidityData infFlowValidityData = setUpInfFlowValidityGoal(validityGoal,
                        contract, anonymisationHeaps, services, variables, exceptionParameter,
                        heaps, localInVariables, localOutVariables, application, instantiation);
                // do additional inf flow preparations on the usage goal
                setUpInfFlowPartOfUsageGoal(result.head(), infFlowValidityData, updates[0],
                        updates[1], updates[2], tb);
            } else {
                // nothing to prove -> set up trivial goal
                validityGoal.addFormula(new SequentFormula(tb.tt()), false, true);
            }
        }
    }
}
