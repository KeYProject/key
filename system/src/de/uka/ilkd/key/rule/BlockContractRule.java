// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.rule;

import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.expression.literal.BooleanLiteral;
import de.uka.ilkd.key.java.expression.literal.NullLiteral;
import de.uka.ilkd.key.java.expression.operator.NotEquals;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.statement.*;
import de.uka.ilkd.key.java.visitor.ProgramElementReplacer;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.java.visitor.OuterBreakContinueAndReturnReplacer;
import de.uka.ilkd.key.proof.InfFlowCheckInfo;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.StrategyInfoUndoMethod;
import de.uka.ilkd.key.proof.init.BlockExecutionPO;
import de.uka.ilkd.key.proof.init.ContractPO;
import de.uka.ilkd.key.proof.init.InfFlowContractPO;
import de.uka.ilkd.key.proof.init.InfFlowContractPO.IFProofObligationVars;
import de.uka.ilkd.key.proof.init.ProofObligationVars;
import de.uka.ilkd.key.proof.init.SymbolicExecutionPO;
import de.uka.ilkd.key.proof.init.po.snippet.InfFlowPOSnippetFactory;
import de.uka.ilkd.key.proof.init.po.snippet.POSnippetFactory;
import de.uka.ilkd.key.proof.mgt.SpecificationRepository;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.rule.tacletbuilder.RemovePostTacletBuilder;
import de.uka.ilkd.key.rule.tacletbuilder.SplitPostTacletBuilder;
import de.uka.ilkd.key.speclang.BlockContract;
import de.uka.ilkd.key.speclang.BlockContract.Variables;
import de.uka.ilkd.key.strategy.StrategyProperties;
import de.uka.ilkd.key.util.ExtList;
import de.uka.ilkd.key.util.MiscTools;
import de.uka.ilkd.key.util.Pair;

import java.util.*;

public class BlockContractRule implements BuiltInRule {

    public static final BlockContractRule INSTANCE = new BlockContractRule();

    private static final Name NAME = new Name("Block Contract");
    private static final String ANONYMISATION_PREFIX = "anon_";
    private static final TermBuilder TB = TermBuilder.DF;

    private static Term lastFocusTerm;
    private static Instantiation lastInstantiation;

    public static Instantiation instantiate(final Term formula,
                                            final Goal goal,
                                            final Services services) {
        if (formula == lastFocusTerm) {
            return lastInstantiation;
        }
        else {
            final Instantiation result =
                    new Instantiator(formula, goal, services).instantiate();
            lastFocusTerm = formula;
            lastInstantiation = result;
            return result;
        }
    }

    public static ImmutableSet<BlockContract> getApplicableContracts(final Instantiation instantiation,
                                                                     final Goal goal,
                                                                     final Services services) {
        if (instantiation == null) {
            return DefaultImmutableSet.nil();
        }
        return getApplicableContracts(services.getSpecificationRepository(),
                                      instantiation.block,
                                      instantiation.modality, goal);
    }

    private static Term buildAfterVar(Term varTerm,
                                      String suffix,
                                      Services services) {
        if (varTerm == null) {
            return null;
        }
        assert varTerm.op() instanceof LocationVariable;        

        KeYJavaType resultType = ((LocationVariable)varTerm.op()).getKeYJavaType();
        if (!suffix.equalsIgnoreCase("")) {
            suffix = new String("_" + suffix);
        }
        String name = TermBuilder.DF.newName(services, varTerm.toString() + "_After" + suffix);
        LocationVariable varAtPostVar =
                new LocationVariable(new ProgramElementName(name), resultType);
        register(varAtPostVar, services);
        Term varAtPost = TermBuilder.DF.var(varAtPostVar);
        return varAtPost;
    }

    private static ImmutableList<Term> buildLocalIns(ImmutableList<Term> varTerms,
                                                     Services services) {
        if (varTerms == null || varTerms.isEmpty()) {
            return varTerms;
        }
        ImmutableList<Term> renamedLocalIns = ImmutableSLList.<Term>nil();
        for(Term varTerm: varTerms) {
            assert varTerm.op() instanceof LocationVariable;        

            KeYJavaType resultType = ((LocationVariable)varTerm.op()).getKeYJavaType();

            String name = TermBuilder.DF.newName(services, varTerm.toString() + "_Before");
            LocationVariable varAtPreVar =
                    new LocationVariable(new ProgramElementName(name), resultType);
            register(varAtPreVar, services);
            Term varAtPre = TermBuilder.DF.var(varAtPreVar);
            renamedLocalIns = renamedLocalIns.append(varAtPre);
        }
        return renamedLocalIns;
    }

    private static ImmutableList<Term> buildLocalOuts(ImmutableList<Term> varTerms,
                                                      Services services) {
        if (varTerms == null || varTerms.isEmpty()) {
            return varTerms;
        }
        ImmutableList<Term> renamedLocalOuts = ImmutableSLList.<Term>nil();
        for(Term varTerm: varTerms) {
            assert varTerm.op() instanceof LocationVariable;        

            KeYJavaType resultType = ((LocationVariable)varTerm.op()).getKeYJavaType();

            String name = TermBuilder.DF.newName(services, varTerm.toString() + "_After");
            LocationVariable varAtPostVar =
                    new LocationVariable(new ProgramElementName(name), resultType);
            register(varAtPostVar, services);
            Term varAtPost = TermBuilder.DF.var(varAtPostVar);
            renamedLocalOuts = renamedLocalOuts.append(varAtPost);
        }
        return renamedLocalOuts;
    }

    static void register(ProgramVariable pv,
                         Services services) {
        Namespace progVarNames = services.getNamespaces().programVariables();
        if (pv != null && progVarNames.lookup(pv.name()) == null) {
            progVarNames.addSafely(pv);
        }
    }

    private static FindTaclet loadFindTaclet(BlockContract contract, Services services) {
        Taclet res = null;
        if (!InfFlowContractPO.hasSymbols()) {
            InfFlowContractPO.newSymbols(
                    services.getProof().env().getInitConfig().activatedTaclets());
        }
        for (int j = 0; j < 10000; j++) {
            String prefix =
                    MiscTools.toValidTacletName("unfold computed formula " + j + " of " +
                                                contract.getUniqueName()).toString();
            res = InfFlowContractPO.getTaclet(prefix);
            if (res != null)
                return (FindTaclet)res;
        }
        assert false; // This should not happen
        return null;
    }

    public static Term loadFindTerm(BlockContract contract, Services services) {
        return loadFindTaclet(contract, services).find();
    }

    private static ImmutableSet<BlockContract>
                        getApplicableContracts(final SpecificationRepository specifications,
                                               final StatementBlock block,
                                               final Modality modality,
                                               final Goal goal) {
        ImmutableSet<BlockContract> collectedContracts =
                specifications.getBlockContracts(block, modality);
        if (modality == Modality.BOX) {
            collectedContracts =
                    collectedContracts.union(specifications.getBlockContracts(block, Modality.DIA));
        }
        else if (modality == Modality.BOX_TRANSACTION) {
            collectedContracts =
                    collectedContracts.union(specifications
                            .getBlockContracts(block, Modality.DIA_TRANSACTION));
        }
        return filterAppliedContracts(collectedContracts, goal);
    }
    
    private static ImmutableSet<BlockContract>
                        filterAppliedContracts(final ImmutableSet<BlockContract> collectedContracts,
                                               final Goal goal) {
        ImmutableSet<BlockContract> result = DefaultImmutableSet.<BlockContract>nil();
        for (BlockContract contract : collectedContracts) {
            if (!contractApplied(contract, goal)) {
                result = result.add(contract);
            };
        }
        return result;
    }

    // This seems to be inefficient...
    private static boolean contractApplied(final BlockContract contract,
                                           final Goal goal)
    {
        Node selfOrParentNode = goal.node();
        while (selfOrParentNode != null) {
            RuleApp app = selfOrParentNode.getAppliedRuleApp();
            if (app instanceof BlockContractBuiltInRuleApp) {
                BlockContractBuiltInRuleApp blockRuleApp =
                        (BlockContractBuiltInRuleApp)app;
                if (blockRuleApp.getBlock().equals(contract.getBlock())) {
                    return true;
                };
            }
            selfOrParentNode = selfOrParentNode.parent();
        }

        Services services = goal.proof().getServices();
        Proof proof = goal.proof();
        ContractPO po = services.getSpecificationRepository().getPOForProof(proof);
        if (po instanceof SymbolicExecutionPO) {
            Goal initiatingGoal = ((SymbolicExecutionPO)po).getInitiatingGoal();
            return contractApplied(contract, initiatingGoal);
        } else if (po instanceof BlockExecutionPO) {
            Goal initiatingGoal = ((BlockExecutionPO)po).getInitiatingGoal();
            return contractApplied(contract, initiatingGoal);
        } else {
            return false;
        }
    }
    
    private BlockContractRule() {
    }

    @Override
    public boolean isApplicable(final Goal goal, final PosInOccurrence occurrence)
    {
        if (occursNotAtTopLevelInSuccedent(occurrence)) {
            return false;
        }
        final Instantiation instantiation =
                instantiate(occurrence.subTerm(), goal, goal.proof().getServices());
        if (instantiation == null) {
            return false;
        }
        final ImmutableSet<BlockContract> contracts =
                getApplicableContracts(instantiation, goal, goal.proof().getServices());
        return !contracts.isEmpty();
    }

    private Pair<Term, Term> buildInfFlowAssumptions(InfFlowData infData) {
        Term beforeAssumptions = TB.equals(infData.heapAtPre, infData.baseHeap);
        Iterator<Term> newIns = infData.newIns.iterator();
        for (Term locIn: infData.localIns) {
            beforeAssumptions = TB.and(beforeAssumptions, TB.equals(newIns.next(), locIn));
        }
        Term afterAssumptions = TB.and(TB.equals(infData.heapAtPost, infData.baseHeap),
                                       TB.equals(infData.selfAtPost, infData.self),
                                       TB.equals(infData.resultAtPost, infData.result),
                                       TB.equals(infData.exceptionAtPost, infData.exception));
        Iterator<Term> newOuts = infData.newOuts.iterator();        
        for (Term locOut: infData.localOuts) {
            afterAssumptions = TB.and(afterAssumptions, TB.equals(newOuts.next(), locOut));
        }
        afterAssumptions = TB.and(afterAssumptions, infData.applPredTerm);        

        return new Pair<Term, Term> (beforeAssumptions, afterAssumptions);
    }

    private InfFlowValidityData
                buildInfFlowValidityGoal(final Goal goal,
                                         final BlockContract contract,
                                         final Map<LocationVariable, Function> anonymisationHeaps,
                                         final Services services,
                                         final Variables variables,
                                         final List<LocationVariable> heaps,
                                         final ImmutableSet<ProgramVariable> localInVariables,
                                         final ImmutableSet<ProgramVariable> localOutVariables,
                                         final BlockContractBuiltInRuleApp application,
                                         final Instantiation instantiation) {
        boolean loadedInfFlow =
                services.getProof().getSettings()
                .getStrategySettings().getActiveStrategyProperties()
                .getProperty(StrategyProperties.INF_FLOW_CHECK_PROPERTY)
                .equals(StrategyProperties.INF_FLOW_CHECK_TRUE);
        if ((goal.getStrategyInfo(InfFlowCheckInfo.INF_FLOW_CHECK_PROPERTY) != null &&
            goal.getStrategyInfo(InfFlowCheckInfo.INF_FLOW_CHECK_PROPERTY) || loadedInfFlow) &&
            contract.hasModifiesClause() && contract.getRespects() != null) {
            // prepare information flow analysis
            assert anonymisationHeaps.size() == 1 : "information flow " +
                                                    "extension is at the " +
                                                    "moment not compatible " +
                                                    "with the non-base-heap " +
                                                    "setting";

            final LocationVariable baseHeap =
                    services.getTypeConverter().getHeapLDT().getHeap();
            final boolean hasSelf = variables.self != null;
            final boolean hasRes = variables.result != null;
            final boolean hasExc = variables.exception != null;

            final Term heapAtPre = TB.var(variables.remembranceHeaps.get(baseHeap));
            final Name heapAtPostName =
                    new Name(TB.newName(services, "heap_After_BLOCK"));
            final Term heapAtPost =
                    TB.func(new Function(heapAtPostName, heapAtPre.sort(), true));
            final Term self = hasSelf ? TB.var(variables.self) : TB.NULL(services);
            final Term selfAtPost =
                    hasSelf ? buildAfterVar(self, "BLOCK", services) : TB.NULL(services);
            final ImmutableList<Term> localInTerms = MiscTools.toTermList(localInVariables);
            final ImmutableList<Term> newLocalIns = buildLocalIns(localInTerms, services);
            final ImmutableList<Term> localOutTerms = MiscTools.toTermList(localOutVariables);
            final ImmutableList<Term> newLocalOuts = buildLocalOuts(localOutTerms, services);
            Term result = hasRes ? TB.var(variables.result) : TB.NULL(services);
            final Term resultAtPost =
                    hasRes ? buildAfterVar(result, "BLOCK", services) : TB.NULL(services);
            final Term exception = hasExc ? TB.var(variables.exception) : TB.NULL(services);
            final Term exceptionAtPost =
                    hasExc ? buildAfterVar(exception, "BLOCK", services) : TB.NULL(services);

            final InfFlowBlockContractTacletBuilder ifContractBuilder =
                    new InfFlowBlockContractTacletBuilder(services);
            ifContractBuilder.setContract(contract);
            ifContractBuilder.setContextUpdate(); // updates are handled by setUpUsageGoal
            ifContractBuilder.setHeapAtPre(heapAtPre);
            ifContractBuilder.setHeapAtPost(heapAtPost);
            if (hasSelf)
                ifContractBuilder.setSelf(self);
            if (hasSelf)
                ifContractBuilder.setSelfAtPost(selfAtPost);
            ifContractBuilder.setLocalIns(newLocalIns);
            ifContractBuilder.setLocalOuts(newLocalOuts);
            if (hasRes)
                ifContractBuilder.setResult(result);
            if (hasRes)
                ifContractBuilder.setResultAtPost(resultAtPost);
            if (hasExc)
                ifContractBuilder.setException(exception);
            if (hasExc)
                ifContractBuilder.setExceptionAtPost(exceptionAtPost);

            // generate information flow contract application predicate
            // and associated taclet
            final Term contractApplTerm =
                    ifContractBuilder.buildContractApplPredTerm(true);
            if (!InfFlowContractPO.hasSymbols()) {
                InfFlowContractPO.newSymbols(
                        services.getProof().env().getInitConfig().activatedTaclets());
            }
            Taclet informationFlowContractApp = ifContractBuilder.buildContractApplTaclet(true);

            InfFlowData infFlowData = new InfFlowData(heapAtPre, heapAtPost, TB.var(heaps.get(0)),
                                                      self, selfAtPost,
                                                      localInTerms, newLocalIns,
                                                      localOutTerms, newLocalOuts,
                                                      result, resultAtPost,
                                                      exception, exceptionAtPost,
                                                      contractApplTerm);
            // TB.var(heaps.get(0)) will be made anonymous by setUpUsageGoal

            // set infFlowAssumptions
            Pair<Term, Term> infFlowAssumptions = buildInfFlowAssumptions(infFlowData);

            // create information flow validity goal

            // generate proof obligation variables
            final ProofObligationVars instantiationVars =
                    new ProofObligationVars(hasSelf ? self : null,
                                            hasSelf ? selfAtPost : null,
                                            newLocalIns,
                                            heapAtPre,
                                            newLocalOuts,
                                            hasRes ? result : null,
                                            hasRes ? resultAtPost : null,
                                            hasExc ? exception : null,
                                            hasExc ? exceptionAtPost : null,
                                            heapAtPost,
                                            services, true);
            final IFProofObligationVars ifVars =
                    new IFProofObligationVars(instantiationVars, services, true);
            application.update(ifVars, instantiation.context);

            // create proof obligation
            InfFlowPOSnippetFactory infFlowFactory =
                POSnippetFactory.getInfFlowFactory(contract, ifVars.c1, ifVars.c2, services);

            Pair<Sequent, Term> seqPostPair =
                    buildBodyPreservesSequent(infFlowFactory, contract, services);
            Sequent seq = seqPostPair.first;
            Term post = seqPostPair.second;

            Goal infFlowGoal = goal.getCleanGoal(seq);
            infFlowGoal.setBranchLabel("Information Flow Validity");

            // create and add split-post and remove-post taclets
            final SplitPostTacletBuilder splitPostTB = new SplitPostTacletBuilder();
            final ArrayList<Taclet> splitPostTaclets = splitPostTB.generateTaclets(post);
            for (final Taclet t : splitPostTaclets) {
                infFlowGoal.addTaclet(t, SVInstantiations.EMPTY_SVINSTANTIATIONS, true);
            }
            final RemovePostTacletBuilder removePostTB = new RemovePostTacletBuilder();
            final ArrayList<Taclet> removePostTaclets = removePostTB.generateTaclets(post);
            for (final Taclet t : removePostTaclets) {
                infFlowGoal.addTaclet(t, SVInstantiations.EMPTY_SVINSTANTIATIONS, true);
            }

            return new InfFlowValidityData(infFlowAssumptions,
                                           informationFlowContractApp,
                                           infFlowGoal);
        } else {
            return new InfFlowValidityData();
        }
    }

    private boolean occursNotAtTopLevelInSuccedent(final PosInOccurrence occurrence)
    {
        return occurrence == null || !occurrence.isTopLevel() || occurrence.isInAntec();
    }

    @Override
    public ImmutableList<Goal> apply(final Goal goal, final Services services,
                                     final RuleApp application) throws RuleAbortException {
        assert application instanceof BlockContractBuiltInRuleApp;
        return apply(goal, services, (BlockContractBuiltInRuleApp) application);
    }

    private ImmutableList<Goal> apply(final Goal goal, final Services services,
                                      final BlockContractBuiltInRuleApp application)
            throws RuleAbortException {
        final Instantiation instantiation =
                instantiate(application.posInOccurrence().subTerm(), goal, services);
        final BlockContract contract = application.getContract();
        assert contract.getBlock().equals(instantiation.block);
        final Term contextUpdate = instantiation.update;
        final List<LocationVariable> heaps = application.getHeapContext();
        final ImmutableSet<ProgramVariable> localInVariables =
                MiscTools.getLocalIns(instantiation.block, services);
        final ImmutableSet<ProgramVariable> localOutVariables =
                MiscTools.getLocalOuts(instantiation.block, services);
        final boolean isStrictlyPure = !application.getContract().hasModifiesClause();
        final Map<LocationVariable, Function> anonymisationHeaps =
                createAndRegisterAnonymisationVariables(heaps, isStrictlyPure, services);
        //final Map<LocationVariable, Function> anonymisationLocalVariables =
        //createAndRegisterAnonymisationVariables(localOutVariables, services);

        final BlockContract.Variables variables = new VariablesCreatorAndRegistrar(
            goal, contract.getPlaceholderVariables(), services
        ).createAndRegister(instantiation.self);

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
        final Term wellFormedAnonymisationHeapsCondition = conditionsAndClausesBuilder
                        .buildWellFormedAnonymisationHeapsCondition(anonymisationHeaps);
        final Term reachableOutCondition =
                conditionsAndClausesBuilder.buildReachableOutCondition(localOutVariables);
        final Term atMostOneFlagSetCondition =
                conditionsAndClausesBuilder.buildAtMostOneFlagSetCondition();

        final UpdatesBuilder updatesBuilder = new UpdatesBuilder(variables, services);
        final Term remembranceUpdate = updatesBuilder.buildRemembranceUpdate(heaps);
        final Term anonymisationUpdate =
                updatesBuilder.buildAnonymisationUpdate(anonymisationHeaps,
                                                        /*anonymisationLocalVariables, */
                                                        modifiesClauses);


        InfFlowValidityData infFlowValitidyData =
                buildInfFlowValidityGoal(goal, contract, anonymisationHeaps, services,
                                         variables, heaps, localInVariables,
                                         localOutVariables, application, instantiation);

        final GoalsConfigurator configurator = new GoalsConfigurator(instantiation,
                                                                     contract.getLabels(),
                                                                     variables,
                                                                     application.posInOccurrence(),
                                                                     services);

        ImmutableList<Goal> result;
        if (infFlowValitidyData.hasInfFlowGoal()) {
            result = goal.split(2);
            // information flow validity branch has already been set up,
            // it has to be added only
            result = result.append(infFlowValitidyData.goal);
        } else {
            result = goal.split(3);

            configurator.setUpValidityGoal(
                result.tail().tail().head(),
                new Term[] {contextUpdate, remembranceUpdate},
                new Term[] {precondition, wellFormedHeapsCondition, reachableInCondition},
                new Term[] {postcondition, frameCondition/*, atMostOneFlagSetCondition*/}
            );
        }
        configurator.setUpPreconditionGoal(
            result.tail().head(),
            contextUpdate,
            new Term[] {precondition, wellFormedHeapsCondition, reachableInCondition}
        );
        configurator.setUpUsageGoal(
            result.head(),
            new Term[] {contextUpdate, remembranceUpdate, anonymisationUpdate},
            new Term[] {postcondition, wellFormedAnonymisationHeapsCondition, reachableOutCondition,
                        atMostOneFlagSetCondition},
            infFlowValitidyData.assumptions,
            infFlowValitidyData.taclet
        );
        return result;
    }

    private Map<LocationVariable, Function>
                    createAndRegisterAnonymisationVariables(final Iterable<LocationVariable> variables,
                                                            final boolean isStrictlyPure,
                                                            final Services services) {
        Map<LocationVariable, Function> result = new LinkedHashMap<LocationVariable, Function>();
        if (!isStrictlyPure) {
            for (LocationVariable variable : variables) {
                final String anonymisationName =
                        TB.newName(services, ANONYMISATION_PREFIX + variable.name());
                final Function anonymisationFunction =
                        new Function(new Name(anonymisationName), variable.sort(), true);
                services.getNamespaces().functions().addSafely(anonymisationFunction);
                result.put(variable, anonymisationFunction);
            }
        }
        return result;
    }

    @Override
    public BlockContractBuiltInRuleApp createApp(final PosInOccurrence occurrence)
    {
        return new BlockContractBuiltInRuleApp(this, occurrence);
    }

    @Override
    public Name name()
    {
        return NAME;
    }

    @Override
    public String displayName()
    {
        return toString();
    }

    @Override
    public String toString()
    {
        return NAME.toString();
    }

    Pair<Sequent, Term> buildBodyPreservesSequent(InfFlowPOSnippetFactory f, BlockContract contract,
                                                  Services services) {
        Term selfComposedExec =
                f.create(InfFlowPOSnippetFactory.Snippet.SELFCOMPOSED_BLOCK_WITH_PRE_RELATION);
        Term post = f.create(InfFlowPOSnippetFactory.Snippet.INF_FLOW_INPUT_OUTPUT_RELATION);

        final Term finalTerm = TB.imp(selfComposedExec, post);
        Sequent seq =
                Sequent.createSuccSequent(new Semisequent(new SequentFormula(finalTerm)));

        return new Pair<Sequent, Term> (seq, post);
    }


    public static final class Instantiation {

        public final Term update;
        public final Term formula;
        public final Modality modality;
        public final Term self;
        public final StatementBlock block;
        public final ExecutionContext context;

        public Instantiation(final Term update, final Term formula, final Modality modality,
                             final Term self, final StatementBlock block,
                             final ExecutionContext context) {
            assert update != null;
            assert update.sort() == Sort.UPDATE;
            assert formula != null;
            assert formula.sort() == Sort.FORMULA;
            assert modality != null;
            assert block != null;
            this.update = update;
            this.formula = formula;
            this.modality = modality;
            this.self = self;
            this.block = block;
            this.context = context;
        }

        public boolean isTransactional()
        {
            return modality.transaction();
        }

    }

    private static final class Instantiator {

        private final Term formula;
        private final Goal goal;
        private final Services services;

        public Instantiator(final Term formula,
                            final Goal goal,
                            final Services services) {
            this.formula = formula;
            this.goal = goal;
            this.services = services;
        }

        public Instantiation instantiate() {
            final Term update = extractUpdate();
            final Term target = extractUpdateTarget();
            if (!(target.op() instanceof Modality)) {
                return null;
            }
            final Modality modality = (Modality) target.op();
            final StatementBlock block =
                    getFirstBlockInPrefixWithAtLeastOneApplicableContract(modality,
                                                                          target.javaBlock(),
                                                                          goal);
            if (block == null) {
                return null;
            }
            final MethodFrame frame = JavaTools.getInnermostMethodFrame(target.javaBlock(), services);
            final Term self = extractSelf(frame);
            final ExecutionContext context = extractExecutionContext(frame);
            return new Instantiation(update, target, modality, self, block, context);
        }

        private Term extractUpdate() {
            if (formula.op() instanceof UpdateApplication) {
                return UpdateApplication.getUpdate(formula);
            }
            else {
                return TB.skip();
            }
        }

        private Term extractUpdateTarget() {
            if (formula.op() instanceof UpdateApplication) {
                return UpdateApplication.getTarget(formula);
            }
            else {
                return formula;
            }
        }

        private Term extractSelf(final MethodFrame frame) {
            if (frame == null) {
                return null;
            }
            return MiscTools.getSelfTerm(frame, services);
        }

        private ExecutionContext extractExecutionContext(final MethodFrame frame) {
            if (frame == null) {
                return null;
            }
            return (ExecutionContext) frame.getExecutionContext();
        }

        private StatementBlock
                    getFirstBlockInPrefixWithAtLeastOneApplicableContract(final Modality modality,
                                                                          final JavaBlock java,
                                                                          final Goal goal) {
            SourceElement element = java.program().getFirstElement();
            while ((element instanceof ProgramPrefix || element instanceof CatchAllStatement)
                    && !(element instanceof StatementBlock && ((StatementBlock) element).isEmpty())) {
                if (element instanceof StatementBlock
                        && hasApplicableContracts((StatementBlock) element, modality, goal)) {
                    return (StatementBlock) element;
                }
                else if (element instanceof StatementContainer) {
                    element = ((StatementContainer) element).getStatementAt(0);
                }
                else {
                    element = element.getFirstElement();
                }
            }
            return null;
        }

        private boolean hasApplicableContracts(final StatementBlock block,
                                               final Modality modality,
                                               Goal goal) {
            return !getApplicableContracts(services.getSpecificationRepository(),
                                           block, modality, goal).isEmpty();
        }

    }

    private static final class VariablesCreatorAndRegistrar {

        private final Goal goal;
        private final BlockContract.Variables placeholderVariables;
        private final Services services;

        public VariablesCreatorAndRegistrar(final Goal goal,
                                            final BlockContract.Variables placeholderVariables,
                                            final Services services) {
            this.goal = goal;
            this.placeholderVariables = placeholderVariables;
            this.services = services;
        }

        public BlockContract.Variables createAndRegister(Term self)
        {
            return new BlockContract.Variables(
                self.op(ProgramVariable.class),
                createAndRegisterFlags(placeholderVariables.breakFlags),
                createAndRegisterFlags(placeholderVariables.continueFlags),
                createAndRegisterVariable(placeholderVariables.returnFlag),
                createAndRegisterVariable(placeholderVariables.result),
                createAndRegisterVariable(placeholderVariables.exception),
                createAndRegisterRemembranceVariables(placeholderVariables.remembranceHeaps),
                createAndRegisterRemembranceVariables(placeholderVariables.remembranceLocalVariables)
            );
        }

        private Map<Label, ProgramVariable> createAndRegisterFlags(final Map<Label,
                                                                   ProgramVariable> placeholderFlags) {
            Map<Label, ProgramVariable> result = new LinkedHashMap<Label, ProgramVariable>();
            for (Map.Entry<Label, ProgramVariable> flag : placeholderFlags.entrySet()) {
                result.put(flag.getKey(), createAndRegisterVariable(flag.getValue()));
            }
            return result;
        }

        private Map<LocationVariable, LocationVariable>
                        createAndRegisterRemembranceVariables(final Map<LocationVariable,
                                                              LocationVariable> remembranceVariables) {
            final Map<LocationVariable, LocationVariable> result =
                    new LinkedHashMap<LocationVariable, LocationVariable>();
            for (Map.Entry<LocationVariable, LocationVariable> remembranceVariable
                    : remembranceVariables.entrySet()) {
                result.put(remembranceVariable.getKey(),
                           createAndRegisterVariable(remembranceVariable.getValue()));
            }
            return result;
        }

        private LocationVariable createAndRegisterVariable(final ProgramVariable placeholderVariable) {
            boolean loadedInfFlow =
                    services.getProof().getSettings()
                    .getStrategySettings().getActiveStrategyProperties()
                    .getProperty(StrategyProperties.INF_FLOW_CHECK_PROPERTY)
                    .equals(StrategyProperties.INF_FLOW_CHECK_TRUE);
            if (placeholderVariable != null) {
                final ProgramElementName newName =
                        new ProgramElementName(
                                TB.newName(services, placeholderVariable.name().toString()));
                final LocationVariable newVariable =
                        new LocationVariable(newName, placeholderVariable.getKeYJavaType());
                if (!loadedInfFlow)
                    goal.addProgramVariable(newVariable);
                return newVariable;
            }
            else {
                return null;
            }
        }

    }

    private static final class UpdatesBuilder extends TermBuilder.Serviced {

        private final BlockContract.Variables variables;

        public UpdatesBuilder(final BlockContract.Variables variables, final Services services)
        {
            super(services);
            this.variables = variables;
        }

        public Term buildRemembranceUpdate(final List<LocationVariable> heaps) {
            Term result = skip();
            for (LocationVariable heap : heaps) {
                final Term update = elementary(variables.remembranceHeaps.get(heap), var(heap));
                result = parallel(result, update);
            }
            for (Map.Entry<LocationVariable, LocationVariable> remembranceVariable
                    : variables.remembranceLocalVariables.entrySet()) {
                result = parallel(result,
                                  elementary(remembranceVariable.getValue(),
                                             var(remembranceVariable.getKey())));
            }
            return result;
        }

        public Term buildAnonymisationUpdate(final Map<LocationVariable, Function> anonymisationHeaps,
                                             /*final Map<LocationVariable, Function>
                                              anonymisationLocalVariables,*/
                                             final Map<LocationVariable, Term> modifiesClauses) {
            Term result = buildLocalVariablesAnonymisationUpdate(/*anonymisationLocalVariables*/);
            for (Map.Entry<LocationVariable, Function> anonymisationHeap
                    : anonymisationHeaps.entrySet()) {
                Term anonymisationUpdate = skip();
                final Term modifiesClause = modifiesClauses.get(anonymisationHeap.getKey());
                if (!modifiesClause.equals(strictlyNothing())) {
                    anonymisationUpdate =
                            anonUpd(anonymisationHeap.getKey(), modifiesClause,
                                    func(anonymisationHeap.getValue()));
                }
                result = parallel(result, anonymisationUpdate);
            }
            return result;
        }

        private Term buildLocalVariablesAnonymisationUpdate(
                /*final Map<LocationVariable, Function> anonymisationLocalVariables,*/) {
            Term result = skip();
            final Collection<LocationVariable> localOutVariables =
                    variables.remembranceLocalVariables.keySet();
            for (LocationVariable variable : localOutVariables) {
                final String anonymisationName = newName(ANONYMISATION_PREFIX + variable.name());
                final Function anonymisationFunction =
                        new Function(new Name(anonymisationName), variable.sort(), true);
                services.getNamespaces().functions().addSafely(anonymisationFunction);
                final Term elementaryUpdate = elementary(variable, func(anonymisationFunction));
                result = parallel(result, elementaryUpdate);
            }
            return result;
            /*Term result = skip();
            for (Map.Entry<LocationVariable, Function> anonymisationLocalVariable :
            anonymisationLocalVariables.entrySet()) {
                result = parallel(result, elementary(anonymisationLocalVariable.getKey(),
                func(anonymisationLocalVariable.getValue())));
            }
            return result;*/
        }

    }

    private static final class ConditionsAndClausesBuilder extends TermBuilder.Serviced {

        private final BlockContract contract;
        private final List<LocationVariable> heaps;
        private final BlockContract.Variables variables;
        private final BlockContract.Terms terms;

        public ConditionsAndClausesBuilder(final BlockContract contract,
                                           final List<LocationVariable> heaps,
                                           final BlockContract.Variables variables,
                                           final Term self, final Services services) {
            super(services);
            this.contract = contract;
            this.heaps = heaps;
            this.variables = variables;
            this.terms = variables.termify(self);
        }

        public Term buildPrecondition() {
            Term result = tt();
            for (LocationVariable heap : heaps) {
                result = and(result,
                             contract.getPrecondition(heap, getBaseHeap(services), terms.self,
                                                      terms.remembranceHeaps, services));
            }
            return result;
        }

        public Term buildWellFormedHeapsCondition() {
            Term result = tt();
            for (LocationVariable heap : heaps) {
                result = and(result, wellFormed(heap));
            }
            return result;
        }

        public Term buildReachableInCondition(final ImmutableSet<ProgramVariable> localInVariables) {
            return buildReachableCondition(localInVariables);
        }

        public Term buildReachableOutCondition(final ImmutableSet<ProgramVariable> localOutVariables) {
            final Term reachableResult =
                    (variables.result != null) ?
                    reachableValue(variables.result) : TB.tt();
            return and(
                buildReachableCondition(localOutVariables),
                reachableResult,
                reachableValue(variables.exception)
            );
        }

        public Term buildReachableCondition(final ImmutableSet<ProgramVariable> variables) {
            Term result = tt();
            for (ProgramVariable variable : variables) {
                result = and(result, reachableValue(variable));
            }
            return result;
        }

        public Map<LocationVariable, Term> buildModifiesClauses() {
            Map<LocationVariable, Term> result = new LinkedHashMap<LocationVariable, Term>();
            for (final LocationVariable heap : heaps) {
                result.put(heap, contract.getModifiesClause(heap, var(heap), terms.self, services));
            }
            return result;
        }

        public Term buildPostcondition() {
            Term result = tt();
            for (LocationVariable heap : heaps) {
                result = and(result, contract.getPostcondition(heap, getBaseHeap(services),
                                                               terms, services));
            }
            return result;
        }

        public Term buildFrameCondition(final Map<LocationVariable, Term> modifiesClauses) {
            Term result = tt();
            Map<LocationVariable, Map<Term, Term>> remembranceVariables =
                    constructRemembranceVariables();
            for (LocationVariable heap : heaps) {
                final Term modifiesClause = modifiesClauses.get(heap);
                final Term frameCondition;
                if (modifiesClause.equals(strictlyNothing()) && var(heap) == getBaseHeap()) {
                    frameCondition = frameStrictlyEmpty(var(heap), remembranceVariables.get(heap));
                }
                else {
                    frameCondition = frame(var(heap), remembranceVariables.get(heap), modifiesClause);
                }
                result = and(result, frameCondition);
            }
            return result;
        }

        private Map<LocationVariable, Map<Term, Term>> constructRemembranceVariables()
        {
            Map<LocationVariable, Map<Term, Term>> result =
                    new LinkedHashMap<LocationVariable, Map<Term, Term>>();
            for (Map.Entry<LocationVariable, LocationVariable> remembranceHeap
                    : variables.remembranceHeaps.entrySet()) {
                final LocationVariable heap = remembranceHeap.getKey();
                result.put(heap, new LinkedHashMap<Term, Term>());
                result.get(heap).put(var(heap), var(remembranceHeap.getValue()));
            }
            for (Map.Entry<LocationVariable, LocationVariable> remembranceLocalVariable
                    : variables.remembranceLocalVariables.entrySet()) {
                result.get(getBaseHeapFunction()).put(var(remembranceLocalVariable.getKey()),
                                                      var(remembranceLocalVariable.getValue()));
            }
            return result;
        }

        private LocationVariable getBaseHeapFunction()
        {
            return services.getTypeConverter().getHeapLDT().getHeap();
        }

        public Term buildWellFormedAnonymisationHeapsCondition(
                final Map<LocationVariable, Function> anonymisationHeaps) {
            Term result = tt();
            for (Function anonymisationFunction : anonymisationHeaps.values()) {
                result = and(result, wellFormed(func(anonymisationFunction)));
            }
            return result;
        }

        public Term buildAtMostOneFlagSetCondition() {
            final List<Term> notSetConditions = new LinkedList<Term>();
            notSetConditions.addAll(buildFlagsNotSetConditions(variables.breakFlags.values()));
            notSetConditions.addAll(buildFlagsNotSetConditions(variables.continueFlags.values()));
            if (variables.returnFlag != null) {
                notSetConditions.add(buildFlagNotSetCondition(variables.returnFlag));
            }
            notSetConditions.add(equals(var(variables.exception), NULL()));

            Term result = tt();
            for (Term notSetCondition : notSetConditions) {
                result = and(result, notSetCondition);
            }
            for (Term onlySetNotSetCondition : notSetConditions) {
                Term condition = not(onlySetNotSetCondition);
                for (Term notSetCondition : notSetConditions) {
                    if (notSetCondition != onlySetNotSetCondition) {
                        condition = and(condition, notSetCondition);
                    }
                }
                result = or(result, condition);
            }
            return result;
        }

        private List<Term> buildFlagsNotSetConditions(final Collection<ProgramVariable> flags) {
            final List<Term> result = new LinkedList<Term>();
            for (ProgramVariable flag : flags) {
                result.add(buildFlagNotSetCondition(flag));
            }
            return result;
        }

        private Term buildFlagNotSetCondition(final ProgramVariable flag) {
            return equals(var(flag), FALSE());
        }

    }

    private static final class GoalsConfigurator {

        private final Instantiation instantiation;
        private final List<Label> labels;
        private final BlockContract.Variables variables;
        private final PosInOccurrence occurrence;
        private final Services services;

        public GoalsConfigurator(final Instantiation instantiation,
                                 final List<Label> labels,
                                 final BlockContract.Variables variables,
                                 final PosInOccurrence occurrence,
                                 final Services services)
        {
            this.instantiation = instantiation;
            this.labels = labels;
            this.variables = variables;
            this.occurrence = occurrence;
            this.services = services;
        }

        public void setUpValidityGoal(final Goal goal, final Term[] updates,
                                      final Term[] assumptions, final Term[] postconditions) {
            goal.setBranchLabel("Validity");
            goal.addFormulaToAntecedent(
                    new SequentFormula(TB.applySequential(updates, TB.and(assumptions))), false);

            final StatementBlock block =
                    new ValidityProgramConstructor(labels, instantiation.block, variables, services)
                            .construct();
            Statement wrappedBlock = wrapInMethodFrameIfContextIsAvailable(block);
            StatementBlock finishedBlock = finishTransactionIfModalityIsTransactional(wrappedBlock);
            goal.changeFormula(new SequentFormula(
                TB.applySequential(
                    updates,
                    TB.prog(instantiation.modality,
                            JavaBlock.createJavaBlock(finishedBlock), TB.and(postconditions)))),
                            occurrence);
            final boolean oldInfFlowCheckInfoValue =
                    goal.getStrategyInfo(InfFlowCheckInfo.INF_FLOW_CHECK_PROPERTY) != null &&
                    goal.getStrategyInfo(InfFlowCheckInfo.INF_FLOW_CHECK_PROPERTY);
            StrategyInfoUndoMethod undo =
                    new StrategyInfoUndoMethod() {

                        @Override
                        public void undo(
                                de.uka.ilkd.key.util.properties.Properties strategyInfos) {
                            strategyInfos.put(InfFlowCheckInfo.INF_FLOW_CHECK_PROPERTY,
                                              oldInfFlowCheckInfoValue);
                        }
                    };
            goal.addStrategyInfo(InfFlowCheckInfo.INF_FLOW_CHECK_PROPERTY, false, undo);
        }

        private Statement wrapInMethodFrameIfContextIsAvailable(final StatementBlock block) {
            if (instantiation.context == null) {
                return block;
            }
            return new MethodFrame(null, instantiation.context, block);
        }

        private StatementBlock finishTransactionIfModalityIsTransactional(final Statement statement) {
            if (instantiation.isTransactional()) {
                return new StatementBlock(new Statement[]
                        {statement,
                         new TransactionStatement(de.uka.ilkd.key.java.recoderext
                                 .TransactionStatement.FINISH)});
            }
            else {
                if (statement instanceof StatementBlock) {
                    return (StatementBlock) statement;
                }
                else {
                    return new StatementBlock(statement);
                }
            }
        }

        public void setUpPreconditionGoal(final Goal goal, final Term update,
                                          final Term[] preconditions) {
            goal.setBranchLabel("Precondition");
            goal.changeFormula(
                    new SequentFormula(TB.apply(update, TB.and(preconditions))), occurrence);
        }

        public void setUpUsageGoal(final Goal goal, final Term[] updates,
                                   final Term[] assumptions, final Pair<Term, Term> infFlowAssumptions,
                                   final Taclet informationFlowContractApp) {
            goal.setBranchLabel("Usage");

            Term uAssumptions = TB.tt();
            if (infFlowAssumptions.equals(new Pair<Term, Term> (TB.tt(), TB.tt()))) {
                uAssumptions =
                        TB.and(TB.applySequential(updates, TB.and(assumptions)));
            } else {
                uAssumptions =
                        TB.and(TB.applySequential(updates, TB.and(assumptions)),
                               TB.applySequential(new Term[] {updates[0], updates[1]},
                                        TB.and(infFlowAssumptions.first,
                                               TB.apply(updates[2], infFlowAssumptions.second))));
            }

            goal.addFormula(new SequentFormula(uAssumptions), true, false);
            goal.changeFormula(new SequentFormula(TB.applySequential(updates, buildUsageFormula())),
                                                  occurrence);
            if (informationFlowContractApp != null) {
                goal.addTaclet(informationFlowContractApp,
                               SVInstantiations.EMPTY_SVINSTANTIATIONS, true);
            }
        }

        private Term buildUsageFormula() {
            return TB.prog(
                instantiation.modality,
                replaceBlock(instantiation.formula.javaBlock(), instantiation.block,
                             constructAbruptTerminationIfCascade()),
                instantiation.formula.sub(0)
            );
        }

        private JavaBlock replaceBlock(final JavaBlock java, final StatementBlock oldBlock,
                                       final StatementBlock newBlock) {
            Statement newProgram =
                    (Statement) new ProgramElementReplacer(java.program(), services)
                            .replace(oldBlock, newBlock);
            return JavaBlock.createJavaBlock(newProgram instanceof StatementBlock
                    ? (StatementBlock) newProgram : new StatementBlock(newProgram));
        }

        private StatementBlock constructAbruptTerminationIfCascade() {
            List<If> ifCascade = new ArrayList<If>();
            for (Map.Entry<Label, ProgramVariable> flag : variables.breakFlags.entrySet()) {
                ifCascade.add(KeYJavaASTFactory
                        .ifThen(flag.getValue(), KeYJavaASTFactory.breakStatement(flag.getKey())));
            }
            for (Map.Entry<Label, ProgramVariable> flag : variables.continueFlags.entrySet()) {
                ifCascade.add(KeYJavaASTFactory
                        .ifThen(flag.getValue(), KeYJavaASTFactory.continueStatement(flag.getKey())));
            }
            if (variables.returnFlag != null) {
                ifCascade.add(KeYJavaASTFactory
                        .ifThen(variables.returnFlag,
                                KeYJavaASTFactory.returnClause(variables.result)));
            }
            ifCascade.add(KeYJavaASTFactory.ifThen(
                new NotEquals(new ExtList(new Expression[] {variables.exception, NullLiteral.NULL})),
                KeYJavaASTFactory.throwClause(variables.exception)));
            return new StatementBlock(ifCascade.toArray(new Statement[ifCascade.size()]));
        }

    }

    public static final class ValidityProgramConstructor {

        private final Iterable<Label> labels;
        private final StatementBlock block;
        private final BlockContract.Variables variables;
        private final Services services;
        private final List<Statement> statements;

        public ValidityProgramConstructor(final Iterable<Label> labels,
                                          final StatementBlock block,
                                          final BlockContract.Variables variables,
                                          final Services services) {
            this.labels = labels;
            this.block = block;
            this.variables = variables;
            this.services = services;
            statements = new LinkedList<Statement>();
        }

        public StatementBlock construct() {
            declareFlagsFalse();
            declareResultDefault();
            declareExceptionNull();
            executeBlockSafely();
            return new StatementBlock(statements.toArray(new Statement[statements.size()]));
        }

        private void declareFlagsFalse() {
            declareFlagsFalse(variables.breakFlags.values());
            declareFlagsFalse(variables.continueFlags.values());
            if (variables.returnFlag != null) {
                declareFlagFalse(variables.returnFlag);
            }
        }

        private void declareFlagsFalse(final Collection<ProgramVariable> flags) {
            for (ProgramVariable flag : flags) {
                declareFlagFalse(flag);
            }
        }

        private void declareFlagFalse(final ProgramVariable flag) {
            statements.add(KeYJavaASTFactory.declare(flag, BooleanLiteral.FALSE,
                           services.getJavaInfo().getKeYJavaType("boolean")));
        }

        private void declareResultDefault()
        {
            if (occursReturnAndIsReturnTypeNotVoid()) {
                KeYJavaType resultType = variables.result.getKeYJavaType();
                statements.add(KeYJavaASTFactory.declare(variables.result,
                                                         resultType.getDefaultValue(), resultType));
            }
        }

        private boolean occursReturnAndIsReturnTypeNotVoid() {
            return variables.returnFlag != null && variables.result != null;
        }

        private void declareExceptionNull() {
            statements.add(KeYJavaASTFactory.declare(variables.exception, NullLiteral.NULL,
                                                     variables.exception.getKeYJavaType()));
        }

        private void executeBlockSafely() {
            final Label breakOutLabel = new ProgramElementName("breakOut");
            final StatementBlock almostSafeBlock =
                    replaceOuterBreaksContinuesAndReturns(block, breakOutLabel);
            final Statement labeledAlmostSafeBlock = label(almostSafeBlock, labels);
            final Statement safeStatement = wrapInTryCatch(labeledAlmostSafeBlock);
            statements.add(new LabeledStatement(breakOutLabel, safeStatement));
        }

        private Statement label(final StatementBlock block, Iterable<Label> labels) {
            Statement result = block;
            for (Label label : labels) {
                result = new LabeledStatement(label, result);
            }
            return result;
        }

        private StatementBlock replaceOuterBreaksContinuesAndReturns(final StatementBlock block,
                                                                     final Label breakOutLabel) {
            return new OuterBreakContinueAndReturnReplacer(
                block, labels, breakOutLabel, variables.breakFlags, variables.continueFlags,
                variables.returnFlag, variables.result, services).replace();
        }

        private Statement wrapInTryCatch(final Statement labeldBlock) {
            ProgramVariable exceptionParameter =
                    createLocalVariable("e", variables.exception.getKeYJavaType());
            Catch katch = KeYJavaASTFactory.catchClause(
                KeYJavaASTFactory.parameterDeclaration(
                        services.getJavaInfo(),
                        exceptionParameter.getKeYJavaType(),
                        exceptionParameter),
                        new StatementBlock(KeYJavaASTFactory
                                .assign(variables.exception, exceptionParameter)));
            return new Try(new StatementBlock(labeldBlock), new Branch[] {katch});
        }

        private ProgramVariable createLocalVariable(final String nameBase, final KeYJavaType type) {
            return KeYJavaASTFactory.localVariable(
                    services.getVariableNamer().getTemporaryNameProposal(nameBase), type);
        }

    }

    private class InfFlowValidityData {
        final Pair<Term, Term> assumptions;
        final Taclet taclet;
        final Goal goal;


        public InfFlowValidityData() {
            assumptions = new Pair<Term, Term> (TB.tt(), TB.tt());
            taclet = null;
            goal = null;
        }

        public InfFlowValidityData(final Pair<Term, Term> assumptions,
                                   final Taclet taclet,
                                   final Goal goal) {
            this.assumptions = assumptions;
            this.taclet = taclet;
            this.goal = goal;
        }

        boolean hasInfFlowGoal() {
            return goal != null;
        }
    }

    private static final class InfFlowData {
        public final Term heapAtPre;
        public final Term heapAtPost;
        public final Term baseHeap;
        public final Term self;
        public final Term selfAtPost;
        public final ImmutableList<Term> localIns;
        public final ImmutableList<Term> newIns;
        public final ImmutableList<Term> localOuts;
        public final ImmutableList<Term> newOuts;
        public final Term result;
        public final Term resultAtPost;
        public final Term exception;
        public final Term exceptionAtPost;
        public final Term applPredTerm;

        public InfFlowData(Term heapAtPre, Term heapAtPost, Term baseHeap,
                           Term self, Term selfAtPost,
                           ImmutableList<Term> localIns, ImmutableList<Term> newIns,
                           ImmutableList<Term> localOuts, ImmutableList<Term> newOuts,
                           Term result, Term resultAtPost,
                           Term exception, Term exceptionAtPost,
                           Term applPredTerm) {
            this.heapAtPre = heapAtPre;
            this.heapAtPost = heapAtPost;
            this.baseHeap = baseHeap;
            this.self = self;
            this.selfAtPost = selfAtPost;
            this.localIns = localIns;
            this.newIns = newIns;
            this.localOuts = localOuts;
            this.newOuts = newOuts;
            this.result = result;
            this.resultAtPost = resultAtPost;
            this.exception = exception;
            this.exceptionAtPost = exceptionAtPost;
            this.applPredTerm = applPredTerm;
        }
    }
}