package de.uka.ilkd.key.rule;

import java.util.List;
import java.util.Map;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSet;

import de.uka.ilkd.key.informationflow.proof.InfFlowCheckInfo;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.label.TermLabelState;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.init.FunctionalBlockContractPO;
import de.uka.ilkd.key.proof.mgt.ComplexRuleJustificationBySpec;
import de.uka.ilkd.key.proof.mgt.RuleJustificationBySpec;
import de.uka.ilkd.key.rule.BlockContractBuilders.ConditionsAndClausesBuilder;
import de.uka.ilkd.key.rule.BlockContractBuilders.GoalsConfigurator;
import de.uka.ilkd.key.rule.BlockContractBuilders.UpdatesBuilder;
import de.uka.ilkd.key.rule.BlockContractBuilders.VariablesCreatorAndRegistrar;
import de.uka.ilkd.key.speclang.BlockContract;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.util.MiscTools;

/**
 * <p>Rule for the application of {@link BlockContract}s.</p>
 *
 * <p> This splits the goal into two branches:
 *    <ol>
 *      <li> Precondition </li>
 *      <li> Usage </li>
 *    </ol>
 * </p>
 *
 * <p> The validity of all {@link BlockContract}s that were used in the
 * application of this rule must be proven in a
 * {@link FunctionalBlockContractPO} before the current proof is
 * considered closed.
 * </p>
 *
 * @see BlockContractExternalBuiltInRuleApp
 */
public class BlockContractExternalRule extends AbstractBlockContractRule {

    public static final BlockContractExternalRule INSTANCE = new BlockContractExternalRule();

    private static final Name NAME = new Name("Block Contract (External)");

    private Term lastFocusTerm;

    private Instantiation lastInstantiation;

    private BlockContractExternalRule() { }

    public Term getLastFocusTerm() {
        return lastFocusTerm;
    }


    protected void setLastFocusTerm(Term lastFocusTerm) {
        this.lastFocusTerm = lastFocusTerm;
    }


    public Instantiation getLastInstantiation() {
        return lastInstantiation;
    }

    @Override
    public Name name() {
        return NAME;
    }


    protected void setLastInstantiation(Instantiation lastInstantiation) {
        this.lastInstantiation = lastInstantiation;
    }

    @Override
    public IBuiltInRuleApp createApp(PosInOccurrence pos,
            TermServices services) {
        return new BlockContractExternalBuiltInRuleApp(this, pos);
    }

    @Override
    public boolean isApplicable(final Goal goal, final PosInOccurrence occurrence) {
        return !InfFlowCheckInfo.isInfFlow(goal) && super.isApplicable(goal, occurrence);
    }

    @Override
    public ImmutableList<Goal> apply(final Goal goal, final Services services,
                                     final RuleApp application) throws RuleAbortException {
        assert application instanceof BlockContractExternalBuiltInRuleApp;
        return apply(goal, services, (BlockContractExternalBuiltInRuleApp) application);
    }

    private ImmutableList<Goal> apply(final Goal goal, final Services services,
                                      final BlockContractExternalBuiltInRuleApp application)
                                              throws RuleAbortException {
        if (InfFlowCheckInfo.isInfFlow(goal)) {
            throw new RuleAbortException(
                    "BlockContractRuleSeparate does not support information flow goals!");
        }

        final TermLabelState termLabelState = new TermLabelState();
        final Instantiation instantiation =
                instantiate(application.posInOccurrence().subTerm(), goal, services);
        final BlockContract contract = application.getContract();
        contract.setInstantiationSelf(instantiation.self);
        assert contract.getBlock().equals(instantiation.block);
        final Term contextUpdate = instantiation.update;

        final List<LocationVariable> heaps = application.getHeapContext();
        final ImmutableSet<ProgramVariable> localInVariables =
                MiscTools.getLocalIns(instantiation.block, services);
        final ImmutableSet<ProgramVariable> localOutVariables =
                MiscTools.getLocalOuts(instantiation.block, services);
        final Map<LocationVariable, Function> anonymisationHeaps =
                createAndRegisterAnonymisationVariables(heaps, contract, services);

        final BlockContract.Variables variables = new VariablesCreatorAndRegistrar(
            goal, contract.getPlaceholderVariables(), services
        ).createAndRegister(instantiation.self, true);

        final ConditionsAndClausesBuilder conditionsAndClausesBuilder =
                new ConditionsAndClausesBuilder(contract, heaps, variables,
                                                instantiation.self, services);
        final Term precondition = conditionsAndClausesBuilder.buildPrecondition();
        final Term wellFormedHeapsCondition =
                conditionsAndClausesBuilder.buildWellFormedHeapsCondition();
        final Term reachableInCondition =
                conditionsAndClausesBuilder.buildReachableInCondition(localInVariables);
        final Term selfConditions =
                conditionsAndClausesBuilder.buildSelfConditions(
                        heaps, contract.getMethod(), contract.getKJT(),
                        instantiation.self, services);
        final Map<LocationVariable, Term> modifiesClauses =
                conditionsAndClausesBuilder.buildModifiesClauses();

        final Term postcondition = conditionsAndClausesBuilder.buildPostcondition();
        final Term wellFormedAnonymisationHeapsCondition =
                conditionsAndClausesBuilder
                .buildWellFormedAnonymisationHeapsCondition(anonymisationHeaps);
        final Term reachableOutCondition =
                conditionsAndClausesBuilder.buildReachableOutCondition(localOutVariables);
        final Term atMostOneFlagSetCondition =
                conditionsAndClausesBuilder.buildAtMostOneFlagSetCondition();

        final UpdatesBuilder updatesBuilder = new UpdatesBuilder(variables, services);
        final Term remembranceUpdate = updatesBuilder.buildRemembranceUpdate(heaps);
        final Term anonymisationUpdate =
                updatesBuilder.buildAnonOutUpdate(anonymisationHeaps, modifiesClauses);
        final ImmutableList<Goal> result;
        final GoalsConfigurator configurator =
            new GoalsConfigurator(application, termLabelState, instantiation,
                                  contract.getLabels(), variables,
                                  application.posInOccurrence(),
                                  services, this);
        result = goal.split(2);

        configurator.setUpPreconditionGoal(result.tail().head(),
                                           contextUpdate,
                                           new Term[] {precondition,
                                                       wellFormedHeapsCondition,
                                                       reachableInCondition,
                                                       selfConditions});
        configurator.setUpUsageGoal(result.head(),
                                    new Term[] {contextUpdate, remembranceUpdate,
                                                anonymisationUpdate},
                                    new Term[] {postcondition,
                                                wellFormedAnonymisationHeapsCondition,
                                                reachableOutCondition,
                                                atMostOneFlagSetCondition});

        final ComplexRuleJustificationBySpec cjust =
            (ComplexRuleJustificationBySpec)
                goal.proof().getInitConfig().getJustifInfo().getJustification(this);

        for (Contract c : contract.getFunctionalContracts()) {
            cjust.add(application, new RuleJustificationBySpec(c));
        }

        return result;
    }
}
