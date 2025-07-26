/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.informationflow.rule;

import java.util.List;
import java.util.Map;
import java.util.Objects;

import de.uka.ilkd.key.informationflow.po.IFProofObligationVars;
import de.uka.ilkd.key.informationflow.proof.InfFlowProof;
import de.uka.ilkd.key.informationflow.rule.tacletbuilder.InfFlowBlockContractTacletBuilder;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.calculus.JavaDLSequentKit;
import de.uka.ilkd.key.proof.init.ProofObligationVars;
import de.uka.ilkd.key.rule.AuxiliaryContractBuilders.ConditionsAndClausesBuilder;
import de.uka.ilkd.key.rule.AuxiliaryContractBuilders.GoalsConfigurator;
import de.uka.ilkd.key.rule.AuxiliaryContractBuilders.UpdatesBuilder;
import de.uka.ilkd.key.rule.BlockContractInternalBuiltInRuleApp;
import de.uka.ilkd.key.rule.BlockContractInternalRule;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.speclang.AuxiliaryContract;
import de.uka.ilkd.key.speclang.BlockContract;
import de.uka.ilkd.key.util.MiscTools;
import de.uka.ilkd.key.wd.WellDefinednessCheck;

import org.key_project.logic.Name;
import org.key_project.logic.op.Function;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.sequent.SequentFormula;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSet;

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
public class InfFlowBlockContractInternalRule extends BlockContractInternalRule {

    /**
     * The only instance of this class.
     */
    public static final InfFlowBlockContractInternalRule INSTANCE =
        new InfFlowBlockContractInternalRule();

    /**
     * This rule's name.
     */
    private static final Name NAME = new Name("InfFlow Block Contract (Internal)");

    /**
     * @see #getLastFocusTerm()
     */
    private JTerm lastFocusTerm;

    /**
     * @see #getLastInstantiation()
     */
    private Instantiation lastInstantiation;

    private InfFlowBlockContractInternalRule() {
        super();
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
    private static ImmutableList<Goal> splitIntoGoals(final Goal goal, final BlockContract contract,
            final List<LocationVariable> heaps,
            final ImmutableSet<LocationVariable> localInVariables,
            final Map<LocationVariable, Function> anonymisationHeaps,
            final JTerm contextUpdate,
            final JTerm remembranceUpdate, final ImmutableSet<LocationVariable> localOutVariables,
            final GoalsConfigurator configurator, final Services services) {
        final ImmutableList<Goal> result;
        final LocationVariable heap = heaps.getFirst();
        if (WellDefinednessCheck.isOn()) {
            result = goal.split(4);
            final JTerm localAnonUpdate = createLocalAnonUpdate(localOutVariables, services);
            final JTerm wdUpdate =
                services.getTermBuilder().parallel(contextUpdate, remembranceUpdate);
            configurator.setUpWdGoal(result.tail().tail().tail().head(), contract, wdUpdate,
                localAnonUpdate, heap, anonymisationHeaps.get(heap), localInVariables);
        } else {
            result = goal.split(3);
        }
        return result;
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
    public BlockContractInternalBuiltInRuleApp createApp(final PosInOccurrence occurrence,
            TermServices services) {
        return new BlockContractInternalBuiltInRuleApp(this, occurrence);
    }

    /**
     * Sets up the validity goal as the first goal in the list.
     *
     * @param result the new goals.
     * @param isInfFlow whether or not this is an information flow proof.
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
    @Override
    protected void setUpValidityGoal(final ImmutableList<Goal> result, final boolean isInfFlow,
            final BlockContract contract, final BlockContractInternalBuiltInRuleApp application,
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
        assert validityGoal != null;

        final ProgramVariable exceptionParameter =
            createLocalVariable("e", variables.exception.getKeYJavaType(), services);
        validityGoal.setBranchLabel("Information Flow Validity");

        // clear goal
        validityGoal.node().setSequent(JavaDLSequentKit.getInstance().getEmptySequent());
        validityGoal.clearAndDetachRuleAppIndex();
        final TermBuilder tb = services.getTermBuilder();

        if (contract.hasModifiableClause(heaps.getFirst()) && contract.hasInfFlowSpecs()) {
            // set up information flow validity goal
            InfFlowValidityData infFlowValidityData = setUpInfFlowValidityGoal(validityGoal,
                contract, anonymisationHeaps, services, variables, exceptionParameter, heaps,
                localInVariables, localOutVariables, application, instantiation);
            // do additional inf flow preparations on the usage goal
            setUpInfFlowPartOfUsageGoal(Objects.requireNonNull(result.head()), infFlowValidityData,
                updates[0],
                updates[1], updates[2], tb);
        } else {
            // nothing to prove -> set up trivial goal
            validityGoal.addFormula(new SequentFormula(tb.tt()), false, true);
        }
    }

    protected InfFlowValidityData setUpInfFlowValidityGoal(final Goal infFlowGoal,
            final BlockContract contract,
            final Map<LocationVariable, Function> anonymisationHeaps,
            final Services services, final AuxiliaryContract.Variables variables,
            final ProgramVariable exceptionParameter, final List<LocationVariable> heaps,
            final ImmutableSet<LocationVariable> localInVariables,
            final ImmutableSet<LocationVariable> localOutVariables,
            final BlockContractInternalBuiltInRuleApp application,
            final Instantiation instantiation) {
        assert heaps.size() == 1 && anonymisationHeaps.size() <= 1
                : "information flow extension is at the moment not "
                    + "compatible with the non-base-heap setting";
        // prepare information flow analysis
        final LocationVariable baseHeap = services.getTypeConverter().getHeapLDT().getHeap();
        final TermBuilder tb = services.getTermBuilder();
        assert infFlowGoal.proof() instanceof InfFlowProof;
        final InfFlowProof proof = (InfFlowProof) infFlowGoal.proof();

        final ImmutableList<JTerm> localIns = MiscTools.toTermList(localInVariables, tb);
        final ImmutableList<JTerm> localOuts = MiscTools.toTermList(localOutVariables, tb);
        final ImmutableList<JTerm> localOutsAtPre = buildLocalOutsAtPre(localOuts, services);
        final ImmutableList<JTerm> localOutsAtPost = buildLocalOutsAtPost(localOuts, services);
        final ImmutableList<JTerm> localInsWithoutOutDuplicates =
            MiscTools.filterOutDuplicates(localIns, localOuts);
        final ImmutableList<JTerm> localVarsAtPre =
            localInsWithoutOutDuplicates.append(localOutsAtPre);
        final ImmutableList<JTerm> localVarsAtPost =
            localInsWithoutOutDuplicates.append(localOutsAtPost);
        final ProofObligationVars instantiationVars = generateProofObligationVariables(variables,
            exceptionParameter, baseHeap, localVarsAtPre, localVarsAtPost, services, tb);
        final IFProofObligationVars ifVars = new IFProofObligationVars(instantiationVars, services);
        application.update(ifVars, instantiation.context());

        // generate information flow contract application predicate and associated taclet
        final InfFlowBlockContractTacletBuilder ifContractBuilder =
            new InfFlowBlockContractTacletBuilder(services);
        ifContractBuilder.setContract(contract);
        ifContractBuilder.setExecutionContext(instantiation.context());
        ifContractBuilder.setContextUpdate(); // updates are handled by setUpUsageGoal
        ifContractBuilder.setProofObligationVars(instantiationVars);
        final JTerm contractApplTerm = ifContractBuilder.buildContractApplPredTerm();
        Taclet informationFlowContractApp = ifContractBuilder.buildTaclet(infFlowGoal);

        // get infFlowAssumptions
        final JTerm infFlowPreAssumption = buildInfFlowPreAssumption(instantiationVars, localOuts,
            localOutsAtPre, tb.var(baseHeap), tb);
        final JTerm infFlowPostAssumption = buildInfFlowPostAssumption(instantiationVars, localOuts,
            localOutsAtPost, tb.var(baseHeap), contractApplTerm, tb);
        addProofObligation(infFlowGoal, proof, contract, ifVars, instantiation.context(), services);

        proof.addIFSymbol(contractApplTerm);
        proof.addIFSymbol(informationFlowContractApp);
        proof.addGoalTemplates(informationFlowContractApp);
        return new InfFlowValidityData(infFlowPreAssumption, infFlowPostAssumption,
            informationFlowContractApp);
    }

    protected void setUpInfFlowPartOfUsageGoal(final Goal usageGoal,
            InfFlowValidityData infFlowValitidyData, final JTerm contextUpdate,
            final JTerm remembranceUpdate, final JTerm anonymisationUpdate, final TermBuilder tb) {
        usageGoal.addTaclet(infFlowValitidyData.taclet, SVInstantiations.EMPTY_SVINSTANTIATIONS,
            true);
        final JTerm uAssumptions =
            tb.applySequential(new JTerm[] { contextUpdate, remembranceUpdate },
                tb.and(infFlowValitidyData.preAssumption,
                    tb.apply(anonymisationUpdate, infFlowValitidyData.postAssumption)));
        usageGoal.addFormula(new SequentFormula(uAssumptions), true, false);
    }


    protected static class InfFlowValidityData {
        final JTerm preAssumption;
        final JTerm postAssumption;
        final Taclet taclet;

        public InfFlowValidityData(final JTerm preAssumption, final JTerm postAssumption,
                final Taclet taclet) {
            this.preAssumption = preAssumption;
            this.postAssumption = postAssumption;
            this.taclet = taclet;
        }
    }
}
