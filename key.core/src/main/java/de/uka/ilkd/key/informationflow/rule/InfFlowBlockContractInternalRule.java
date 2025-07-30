/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.informationflow.rule;

import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Objects;

import de.uka.ilkd.key.informationflow.po.BlockExecutionPO;
import de.uka.ilkd.key.informationflow.po.IFProofObligationVars;
import de.uka.ilkd.key.informationflow.po.SymbolicExecutionPO;
import de.uka.ilkd.key.informationflow.po.snippet.InfFlowPOSnippetFactory;
import de.uka.ilkd.key.informationflow.po.snippet.POSnippetFactory;
import de.uka.ilkd.key.informationflow.proof.InfFlowCheckInfo;
import de.uka.ilkd.key.informationflow.proof.InfFlowProof;
import de.uka.ilkd.key.informationflow.proof.init.StateVars;
import de.uka.ilkd.key.informationflow.rule.tacletbuilder.InfFlowBlockContractTacletBuilder;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.statement.JavaStatement;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.label.ParameterlessTermLabel;
import de.uka.ilkd.key.logic.op.JFunction;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.calculus.JavaDLSequentKit;
import de.uka.ilkd.key.proof.init.FunctionalBlockContractPO;
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
import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;
import org.key_project.util.collection.ImmutableSet;

import org.jspecify.annotations.Nullable;

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
    protected ImmutableList<Goal> splitIntoGoals(final Goal goal, final BlockContract contract,
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
    protected void setUpValidityGoal(final ImmutableList<Goal> result,
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
        var app = (InfFlowBlockContractInternalBuiltInRuleApp) application;

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
                localInVariables, localOutVariables, app, instantiation);
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
            final InfFlowBlockContractInternalBuiltInRuleApp application,
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

    /**
     *
     * @param contract a block contract.
     * @param goal the current goal.
     * @return {@code true} if the contract has already been applied.
     */
    protected static boolean contractApplied(final BlockContract contract, final Goal goal) {
        var po = getAppliedProofObligation(contract, goal);
        return switch (po) {
            case FunctionalBlockContractPO functionalBlockContractPO when contract.getBlock()
                    .equals(functionalBlockContractPO.getBlock()) ->
                true;
            case SymbolicExecutionPO symbolicExecutionPO -> {
                Goal initiatingGoal = symbolicExecutionPO.getInitiatingGoal();
                yield contractApplied(contract, initiatingGoal);
            }
            case BlockExecutionPO blockExecutionPO -> {
                Goal initiatingGoal = blockExecutionPO.getInitiatingGoal();
                yield contractApplied(contract, initiatingGoal);
            }
            case null, default -> false;
        };
    }


    static SequentFormula buildBodyPreservesSequent(
            InfFlowPOSnippetFactory f, InfFlowProof proof) {
        JTerm selfComposedExec =
            f.create(InfFlowPOSnippetFactory.Snippet.SELFCOMPOSED_BLOCK_WITH_PRE_RELATION);
        JTerm post = f.create(InfFlowPOSnippetFactory.Snippet.INF_FLOW_INPUT_OUTPUT_RELATION);
        final TermBuilder tb = proof.getServices().getTermBuilder();

        final JTerm finalTerm =
            tb.imp(tb.label(selfComposedExec, ParameterlessTermLabel.SELF_COMPOSITION_LABEL), post);
        proof.addLabeledIFSymbol(selfComposedExec);

        return new SequentFormula(finalTerm);
    }

    protected static ProofObligationVars generateProofObligationVariables(
            final AuxiliaryContract.Variables variables, final ProgramVariable exceptionParameter,
            final LocationVariable baseHeap, final ImmutableList<JTerm> localVarsAtPre,
            final ImmutableList<JTerm> localVarsAtPost, final Services services,
            final TermBuilder tb) {
        final boolean hasSelf = variables.self != null;
        final boolean hasRes = variables.result != null;
        final boolean hasExc = variables.exception != null;

        final JTerm heapAtPre = tb.var(variables.remembranceHeaps.get(baseHeap));
        final Name heapAtPostName = new Name(tb.newName("heap_After_BLOCK"));
        final JTerm heapAtPost = tb.func(new JFunction(heapAtPostName, heapAtPre.sort(), true));
        final JTerm selfAtPre = hasSelf ? tb.var(variables.self) : tb.NULL();
        final JTerm selfAtPost = hasSelf ? buildAfterVar(selfAtPre, "BLOCK", services) : tb.NULL();

        JTerm resultAtPre = hasRes ? tb.var(variables.result) : tb.NULL();
        final JTerm resultAtPost =
            hasRes ? buildAfterVar(resultAtPre, "BLOCK", services) : tb.NULL();
        final JTerm exceptionAtPre = hasExc ? tb.var(variables.exception) : tb.NULL();
        final JTerm exceptionAtPost =
            hasExc ? buildAfterVar(exceptionAtPre, "BLOCK", services) : tb.NULL();

        // generate proof obligation variables
        final StateVars instantiationPreVars = new StateVars(hasSelf ? selfAtPre : null,
            localVarsAtPre, hasRes ? resultAtPre : null, hasExc ? exceptionAtPre : null, heapAtPre);
        final StateVars instantiationPostVars =
            new StateVars(hasSelf ? selfAtPost : null, localVarsAtPost,
                hasRes ? resultAtPost : null, hasExc ? exceptionAtPost : null, heapAtPost);
        final ProofObligationVars instantiationVars = new ProofObligationVars(instantiationPreVars,
            instantiationPostVars, tb.var(exceptionParameter), null, tb);
        return instantiationVars;
    }

    protected static void addProofObligation(final Goal infFlowGoal, final InfFlowProof proof,
            final BlockContract contract, final IFProofObligationVars ifVars,
            final ExecutionContext ec, final Services services) {
        // create proof obligation
        InfFlowPOSnippetFactory infFlowFactory =
            POSnippetFactory.getInfFlowFactory(contract, ifVars.c1, ifVars.c2, ec, services);

        final SequentFormula poFormula =
            buildBodyPreservesSequent(infFlowFactory, proof);

        // add proof obligation to goal
        infFlowGoal.addFormula(poFormula, false, true);
    }

    /**
     *
     * @param collectedContracts a set of block contracts.
     * @param goal the current goal.
     * @return the set with all non-applicable contracts filtered out.
     */
    protected static ImmutableSet<BlockContract> filterAppliedContracts(
            final ImmutableSet<BlockContract> collectedContracts, final Goal goal) {
        ImmutableSet<BlockContract> result = DefaultImmutableSet.nil();
        for (BlockContract contract : collectedContracts) {
            if (!contractApplied(contract, goal) || InfFlowCheckInfo.isInfFlow(goal)) {
                result = result.add(contract);
            }
        }
        return result;
    }

    /*
     * Factory methods for information flow contracts.
     *
     * TODO These could be moved into a separate class (like BlockContractBuilders) to allow them to
     * be reused in other classes.
     */
    protected static @Nullable JTerm buildAfterVar(JTerm varTerm, String suffix,
            Services services) {
        if (varTerm == null) {
            return null;
        }
        assert varTerm.op() instanceof LocationVariable;

        final TermBuilder tb = services.getTermBuilder();
        KeYJavaType resultType = ((LocationVariable) varTerm.op()).getKeYJavaType();
        if (!suffix.equalsIgnoreCase("")) {
            suffix = "_" + suffix;
        }
        String name = tb.newName(varTerm + "_After" + suffix);
        LocationVariable varAtPostVar =
            new LocationVariable(new ProgramElementName(name), resultType);
        register(varAtPostVar, services);
        JTerm varAtPost = tb.var(varAtPostVar);
        return varAtPost;
    }


    protected static ImmutableList<JTerm> buildLocalOutsAtPre(ImmutableList<JTerm> varTerms,
            Services services) {
        if (varTerms == null || varTerms.isEmpty()) {
            return varTerms;
        }
        final TermBuilder tb = services.getTermBuilder();
        ImmutableList<JTerm> renamedLocalOuts = ImmutableSLList.nil();
        for (JTerm varTerm : varTerms) {
            assert varTerm.op() instanceof LocationVariable;

            KeYJavaType resultType = ((LocationVariable) varTerm.op()).getKeYJavaType();

            String name = tb.newName(varTerm + "_Before");
            LocationVariable varAtPostVar =
                new LocationVariable(new ProgramElementName(name), resultType);
            register(varAtPostVar, services);
            JTerm varAtPost = tb.var(varAtPostVar);
            renamedLocalOuts = renamedLocalOuts.append(varAtPost);
        }
        return renamedLocalOuts;
    }

    protected static ImmutableList<JTerm> buildLocalOutsAtPost(ImmutableList<JTerm> varTerms,
            Services services) {
        if (varTerms == null || varTerms.isEmpty()) {
            return varTerms;
        }
        final TermBuilder tb = services.getTermBuilder();
        ImmutableList<JTerm> renamedLocalOuts = ImmutableSLList.nil();
        for (JTerm varTerm : varTerms) {
            assert varTerm.op() instanceof LocationVariable;

            KeYJavaType resultType = ((LocationVariable) varTerm.op()).getKeYJavaType();

            String name = tb.newName(varTerm + "_After");
            LocationVariable varAtPostVar =
                new LocationVariable(new ProgramElementName(name), resultType);
            register(varAtPostVar, services);
            JTerm varAtPost = tb.var(varAtPostVar);
            renamedLocalOuts = renamedLocalOuts.append(varAtPost);
        }
        return renamedLocalOuts;
    }

    protected static JTerm buildInfFlowPreAssumption(ProofObligationVars instVars,
            ImmutableList<JTerm> localOuts, ImmutableList<JTerm> localOutsAtPre, JTerm baseHeap,
            final TermBuilder tb) {
        JTerm beforeAssumptions = tb.equals(instVars.pre.heap, baseHeap);
        Iterator<JTerm> outsAtPre = localOutsAtPre.iterator();
        for (JTerm locOut : localOuts) {
            beforeAssumptions = tb.and(beforeAssumptions, tb.equals(outsAtPre.next(), locOut));
        }
        return beforeAssumptions;
    }

    protected static JTerm buildInfFlowPostAssumption(ProofObligationVars instVars,
            ImmutableList<JTerm> localOuts, ImmutableList<JTerm> localOutsAtPost, JTerm baseHeap,
            JTerm applPredTerm, final TermBuilder tb) {
        JTerm resultEq =
            instVars.pre.result != null ? tb.equals(instVars.post.result, instVars.pre.result)
                    : tb.tt();
        JTerm exceptionEq = instVars.pre.exception != null
                ? tb.equals(instVars.post.exception, instVars.pre.exception)
                : tb.tt();
        JTerm selfEq =
            instVars.pre.self != null ? tb.equals(instVars.post.self, instVars.pre.self) : tb.tt();
        JTerm afterAssumptions =
            tb.and(tb.equals(instVars.post.heap, baseHeap), selfEq, resultEq, exceptionEq);
        Iterator<JTerm> outAtPost = localOutsAtPost.iterator();
        for (JTerm locOut : localOuts) {
            afterAssumptions = tb.and(afterAssumptions, tb.equals(outAtPost.next(), locOut));
        }
        afterAssumptions = tb.and(afterAssumptions, applPredTerm);

        return afterAssumptions;
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

    public static class InfFlowBlockContractInternalBuiltInRuleApp
            extends BlockContractInternalBuiltInRuleApp<InfFlowBlockContractInternalRule> {
        public InfFlowBlockContractInternalBuiltInRuleApp(InfFlowBlockContractInternalRule rule,
                PosInOccurrence occurrence) {
            super(rule, occurrence);
        }

        public InfFlowBlockContractInternalBuiltInRuleApp(InfFlowBlockContractInternalRule rule,
                PosInOccurrence occurrence,
                @Nullable ImmutableList<PosInOccurrence> ifInstantiations,
                @Nullable JavaStatement statement, @Nullable BlockContract contract,
                @Nullable List<LocationVariable> heaps) {
            super(rule, occurrence, ifInstantiations, statement, contract, heaps);
        }

        /**
         * @see #getInformationFlowProofObligationVars()
         */
        protected IFProofObligationVars infFlowVars;

        /**
         *
         * @return set of four sets of ProofObligationVars necessary for information flow proofs.
         */
        public IFProofObligationVars getInformationFlowProofObligationVars() {
            return infFlowVars;
        }

        /**
         * Sets the proof obligation variables and execution context to new values.
         *
         * @param vars new proof obligation variables.
         * @param context new execution context.
         */
        public void update(IFProofObligationVars vars, ExecutionContext context) {
            this.infFlowVars = vars;
            this.context = context;
        }
    }
}
