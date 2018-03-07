package de.uka.ilkd.key.rule;

import java.util.List;
import java.util.Map;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSet;

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
import de.uka.ilkd.key.rule.BlockContractBuilders.ConditionsAndClausesBuilder;
import de.uka.ilkd.key.rule.BlockContractBuilders.GoalsConfigurator;
import de.uka.ilkd.key.rule.BlockContractBuilders.UpdatesBuilder;
import de.uka.ilkd.key.rule.BlockContractBuilders.VariablesCreatorAndRegistrar;
import de.uka.ilkd.key.speclang.LoopContract;
import de.uka.ilkd.key.util.MiscTools;

/**
 * <p>Rule for the application of {@link LoopContract}s.</p>
 * 
 * <p> This splits the goal into two branches:
 *    <ol>
 *      <li> Validity </li>
 *      <li> Precondition </li>
 *      <li> Usage </li>
 *    </ol>
 * </p>
 * 
 * @see LoopContractInternalBuiltInRuleApp
 */
public class LoopContractInternalRule extends AbstractLoopContractRule {
    
    public static final LoopContractInternalRule INSTANCE = new LoopContractInternalRule();

    private static final Name NAME = new Name("Loop Contract (Internal)");

    private Term lastFocusTerm;
    
    private Instantiation lastInstantiation;

    private LoopContractInternalRule() {  }
    
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
    public LoopContractInternalBuiltInRuleApp createApp(final PosInOccurrence occurrence,
                                                 TermServices services) {
        return new LoopContractInternalBuiltInRuleApp(this, occurrence);
    }

    @Override
    public ImmutableList<Goal> apply(final Goal goal, final Services services,
                                     final RuleApp application) throws RuleAbortException {
        assert application instanceof LoopContractInternalBuiltInRuleApp;
        return apply(goal, services, (LoopContractInternalBuiltInRuleApp) application);
    }

    private ImmutableList<Goal> apply(final Goal goal, final Services services,
                                      final LoopContractInternalBuiltInRuleApp application)
                                              throws RuleAbortException {
        final TermLabelState termLabelState = new TermLabelState();
        final Instantiation instantiation =
                instantiate(application.posInOccurrence().subTerm(), goal, services);
        final LoopContract contract = application.getContract();
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

        final LoopContract.Variables variables = new VariablesCreatorAndRegistrar(
            goal, contract.getPlaceholderVariables(), services
        ).createAndRegister(instantiation.self, true);
        final ProgramVariable exceptionParameter =
                    createLocalVariable("e", variables.exception.getKeYJavaType(),
                                        services);
        final LoopContract.Variables nextVariables = new VariablesCreatorAndRegistrar(
                goal, variables, services).createAndRegisterCopies("_NEXT");
                

        final ConditionsAndClausesBuilder conditionsAndClausesBuilder =
                new ConditionsAndClausesBuilder(contract, heaps, variables,
                                                instantiation.self, services);
        final Term precondition = conditionsAndClausesBuilder.buildPrecondition();
        final Term wellFormedHeapsCondition =
                conditionsAndClausesBuilder.buildWellFormedHeapsCondition();
        final Term reachableInCondition =
                conditionsAndClausesBuilder.buildReachableInCondition(localInVariables);
        final Map<LocationVariable, Term> modifiesClauses =
                conditionsAndClausesBuilder.buildModifiesClauses();

        final Term postcondition = conditionsAndClausesBuilder.buildPostcondition();
        final Term frameCondition = conditionsAndClausesBuilder.buildFrameCondition(modifiesClauses);
        final Term wellFormedAnonymisationHeapsCondition =
                conditionsAndClausesBuilder
                .buildWellFormedAnonymisationHeapsCondition(anonymisationHeaps);
        final Term reachableOutCondition =
                conditionsAndClausesBuilder.buildReachableOutCondition(localOutVariables);
        final Term atMostOneFlagSetCondition =
                conditionsAndClausesBuilder.buildAtMostOneFlagSetCondition();
        final Term decreasesCheck =
                conditionsAndClausesBuilder.buildDecreasesCheck();
        final Term nextPostcondition =
                new ConditionsAndClausesBuilder(contract, heaps, nextVariables,
                        instantiation.self, services)
                .buildPostcondition();

        final UpdatesBuilder updatesBuilder = new UpdatesBuilder(variables, services);
        final Term remembranceUpdate = updatesBuilder.buildRemembranceUpdate(heaps);
        final Term anonymisationUpdate =
                updatesBuilder.buildAnonOutUpdate(anonymisationHeaps,
                                                        modifiesClauses);
        
        final Term nextRemembranceUpdate =
                new UpdatesBuilder(nextVariables, services).buildRemembranceUpdate(heaps);
        
        
        final ImmutableList<Goal> result;
        final GoalsConfigurator configurator = new GoalsConfigurator(application,
                                                                     termLabelState,
                                                                     instantiation,
                                                                     contract.getLabels(),
                                                                     variables,
                                                                     application.posInOccurrence(),
                                                                     services,
                                                                     this);
        
        result = goal.split(3);

        configurator.setUpPreconditionGoal(result.tail().head(),
                contextUpdate,
                new Term[] {precondition, wellFormedHeapsCondition,
                        reachableInCondition});
        configurator.setUpUsageGoal(result.head(),
                new Term[] {contextUpdate, remembranceUpdate,
                        anonymisationUpdate},
                new Term[] {postcondition, wellFormedAnonymisationHeapsCondition,
                        reachableOutCondition, atMostOneFlagSetCondition});

        configurator.setUpLoopValidityGoal(
                goal,
                contract,
                contextUpdate,
                remembranceUpdate,
                nextRemembranceUpdate,
                anonymisationHeaps,
                modifiesClauses,
                new Term[] { precondition, wellFormedHeapsCondition, reachableInCondition },
                decreasesCheck,
                new Term[] { postcondition, frameCondition },
                new Term[] { nextPostcondition },
                exceptionParameter,
                variables.termify(instantiation.self),
                nextVariables);

        return result;
    }
}