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

import de.uka.ilkd.key.rule.tacletbuilder.InfFlowBlockContractTacletBuilder;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.JavaTools;
import de.uka.ilkd.key.java.KeYJavaASTFactory;
import de.uka.ilkd.key.java.Label;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.Statement;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.StatementContainer;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.expression.literal.BooleanLiteral;
import de.uka.ilkd.key.java.expression.literal.NullLiteral;
import de.uka.ilkd.key.java.expression.operator.NotEquals;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.statement.Branch;
import de.uka.ilkd.key.java.statement.Catch;
import de.uka.ilkd.key.java.statement.CatchAllStatement;
import de.uka.ilkd.key.java.statement.If;
import de.uka.ilkd.key.java.statement.LabeledStatement;
import de.uka.ilkd.key.java.statement.MethodFrame;
import de.uka.ilkd.key.java.statement.TransactionStatement;
import de.uka.ilkd.key.java.statement.Try;
import de.uka.ilkd.key.java.visitor.OuterBreakContinueAndReturnReplacer;
import de.uka.ilkd.key.java.visitor.ProgramElementReplacer;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.ProgramPrefix;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.label.ParameterlessTermLabel;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.Transformer;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.macros.WellDefinednessMacro;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.InfFlowCheckInfo;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.StrategyInfoUndoMethod;
import de.uka.ilkd.key.proof.init.BlockExecutionPO;
import de.uka.ilkd.key.proof.init.IFProofObligationVars;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.proof.init.StateVars;
import de.uka.ilkd.key.proof.init.SymbolicExecutionPO;
import de.uka.ilkd.key.proof.init.ProofObligationVars;
import de.uka.ilkd.key.proof.init.po.snippet.InfFlowPOSnippetFactory;
import de.uka.ilkd.key.proof.init.po.snippet.POSnippetFactory;
import de.uka.ilkd.key.proof.mgt.SpecificationRepository;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.speclang.BlockContract;
import de.uka.ilkd.key.speclang.BlockContract.Variables;
import de.uka.ilkd.key.speclang.BlockWellDefinedness;
import de.uka.ilkd.key.speclang.WellDefinednessCheck;
import de.uka.ilkd.key.util.ExtList;
import de.uka.ilkd.key.util.MiscTools;

public class BlockContractRule implements BuiltInRule {

    public static final BlockContractRule INSTANCE = new BlockContractRule();

    private static final Name NAME = new Name("Block Contract");
    private static final String ANONYMISATION_PREFIX = "anon_";

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

        final TermBuilder tb = services.getTermBuilder();
        KeYJavaType resultType = ((LocationVariable)varTerm.op()).getKeYJavaType();
        if (!suffix.equalsIgnoreCase("")) {
            suffix = new String("_" + suffix);
        }
        String name = tb.newName(varTerm.toString() + "_After" + suffix);
        LocationVariable varAtPostVar =
                new LocationVariable(new ProgramElementName(name), resultType);
        register(varAtPostVar, services);
        Term varAtPost = tb.var(varAtPostVar);
        return varAtPost;
    }

    private static ImmutableList<Term> buildLocalOutsAtPre(ImmutableList<Term> varTerms,
                                                           Services services) {
        if (varTerms == null || varTerms.isEmpty()) {
            return varTerms;
        }
        final TermBuilder tb = services.getTermBuilder();
        ImmutableList<Term> renamedLocalOuts = ImmutableSLList.<Term>nil();
        for(Term varTerm: varTerms) {
            assert varTerm.op() instanceof LocationVariable;

            KeYJavaType resultType = ((LocationVariable)varTerm.op()).getKeYJavaType();

            String name = tb.newName(varTerm.toString() + "_Before");
            LocationVariable varAtPostVar =
                    new LocationVariable(new ProgramElementName(name), resultType);
            register(varAtPostVar, services);
            Term varAtPost = tb.var(varAtPostVar);
            renamedLocalOuts = renamedLocalOuts.append(varAtPost);
        }
        return renamedLocalOuts;
    }

    private static ImmutableList<Term> buildLocalOutsAtPost(ImmutableList<Term> varTerms,
                                                            Services services) {
        if (varTerms == null || varTerms.isEmpty()) {
            return varTerms;
        }
        final TermBuilder tb = services.getTermBuilder();
        ImmutableList<Term> renamedLocalOuts = ImmutableSLList.<Term>nil();
        for(Term varTerm: varTerms) {
            assert varTerm.op() instanceof LocationVariable;

            KeYJavaType resultType = ((LocationVariable)varTerm.op()).getKeYJavaType();

            String name = tb.newName(varTerm.toString() + "_After");
            LocationVariable varAtPostVar =
                    new LocationVariable(new ProgramElementName(name), resultType);
            register(varAtPostVar, services);
            Term varAtPost = tb.var(varAtPostVar);
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

    private static ImmutableSet<BlockContract>
                        getApplicableContracts(final SpecificationRepository specifications,
                                               final StatementBlock block,
                                               final Modality modality,
                                               final Goal goal) {
        ImmutableSet<BlockContract> collectedContracts =
                specifications.getBlockContracts(block, modality);
        if (modality == Modality.BOX) {
            collectedContracts = collectedContracts.union(
                    specifications.getBlockContracts(block, Modality.DIA));
        }
        else if (modality == Modality.BOX_TRANSACTION) {
            collectedContracts = collectedContracts.union(
                    specifications.getBlockContracts(block, Modality.DIA_TRANSACTION));
        }
        return filterAppliedContracts(collectedContracts, goal);
    }

    private static ImmutableSet<BlockContract>
                        filterAppliedContracts(final ImmutableSet<BlockContract> collectedContracts,
                                               final Goal goal) {
        ImmutableSet<BlockContract> result = DefaultImmutableSet.<BlockContract>nil();
        for (BlockContract contract : collectedContracts) {
            if (!contractApplied(contract, goal) || InfFlowCheckInfo.isInfFlow(goal)) {
                result = result.add(contract);
            }
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
                }
            }
            selfOrParentNode = selfOrParentNode.parent();
        }

        Services services = goal.proof().getServices();
        Proof proof = goal.proof();
        ProofOblInput po = services.getSpecificationRepository().getProofOblInput(proof);
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
    public boolean isApplicable(final Goal goal, final PosInOccurrence occurrence) {
        if (occursNotAtTopLevelInSuccedent(occurrence)) {
            return false;
        }
        // abort if inside of transformer
        if (Transformer.inTransformer(occurrence)) {
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

    private static Term buildInfFlowPreAssumption(ProofObligationVars instVars,
                                                  ImmutableList<Term> localOuts,
                                                  ImmutableList<Term> localOutsAtPre,
                                                  Term baseHeap,
                                                  final TermBuilder tb) {
        Term beforeAssumptions = tb.equals(instVars.pre.heap, baseHeap);
        Iterator<Term> outsAtPre = localOutsAtPre.iterator();
        for (Term locOut: localOuts) {
            beforeAssumptions = tb.and(beforeAssumptions, tb.equals(outsAtPre.next(), locOut));
        }
        return beforeAssumptions;
    }


    private static Term buildInfFlowPostAssumption(ProofObligationVars instVars,
                                                   ImmutableList<Term> localOuts,
                                                   ImmutableList<Term> localOutsAtPost,
                                                   Term baseHeap,
                                                   Term applPredTerm,
                                                   final TermBuilder tb) {
        Term resultEq = instVars.pre.result != null ?
                tb.equals(instVars.post.result, instVars.pre.result) : tb.tt();
        Term exceptionEq = instVars.pre.exception != null ?
                tb.equals(instVars.post.exception, instVars.pre.exception) : tb.tt();
        Term selfEq = instVars.pre.self != null ?
                      tb.equals(instVars.post.self, instVars.pre.self) : tb.tt();
        Term afterAssumptions = tb.and(tb.equals(instVars.post.heap, baseHeap),
                                       selfEq,
                                       resultEq,
                                       exceptionEq);
        Iterator<Term> outAtPost = localOutsAtPost.iterator();
        for (Term locOut: localOuts) {
            afterAssumptions = tb.and(afterAssumptions, tb.equals(outAtPost.next(), locOut));
        }
        afterAssumptions = tb.and(afterAssumptions, applPredTerm);

        return afterAssumptions;
    }

    
    private InfFlowValidityData
                setUpInfFlowValidityGoal(final Goal infFlowGoal,
                                         final BlockContract contract,
                                         final Map<LocationVariable, Function> anonymisationHeaps,
                                         final Services services,
                                         final Variables variables,
                                         final ProgramVariable exceptionParameter,
                                         final List<LocationVariable> heaps,
                                         final ImmutableSet<ProgramVariable> localInVariables,
                                         final ImmutableSet<ProgramVariable> localOutVariables,
                                         final BlockContractBuiltInRuleApp application,
                                         final Instantiation instantiation) {
        assert heaps.size() == 1 &&
               anonymisationHeaps.size() <= 1 : "information flow " +
                                                "extension is at the " +
                                                "moment not compatible " +
                                                "with the non-base-heap " +
                                                "setting";

        // prepare information flow analysis
        final LocationVariable baseHeap =
                services.getTypeConverter().getHeapLDT().getHeap();
        final TermBuilder tb = services.getTermBuilder();
        final Proof proof = infFlowGoal.proof();

        final boolean hasSelf = variables.self != null;
        final boolean hasRes = variables.result != null;
        final boolean hasExc = variables.exception != null;

        final Term heapAtPre = tb.var(variables.remembranceHeaps.get(baseHeap));
        final Name heapAtPostName =
                new Name(tb.newName("heap_After_BLOCK"));
        final Term heapAtPost =
                tb.func(new Function(heapAtPostName, heapAtPre.sort(), true));
        final Term selfAtPre = hasSelf ? tb.var(variables.self) : tb.NULL();
        final Term selfAtPost =
                hasSelf ? buildAfterVar(selfAtPre, "BLOCK", services) : tb.NULL();
        final ImmutableList<Term> localIns = MiscTools.toTermList(localInVariables, tb);
        final ImmutableList<Term> localOuts = MiscTools.toTermList(localOutVariables, tb);
        final ImmutableList<Term> localOutsAtPre = buildLocalOutsAtPre(localOuts, services);
        final ImmutableList<Term> localOutsAtPost = buildLocalOutsAtPost(localOuts, services);
        final ImmutableList<Term> localInsWithoutOutDuplicates =
                MiscTools.filterOutDuplicates(localIns, localOuts);
        final ImmutableList<Term> localVarsAtPre =
                localInsWithoutOutDuplicates.append(localOutsAtPre);
        final ImmutableList<Term> localVarsAtPost =
                localInsWithoutOutDuplicates.append(localOutsAtPost);
        Term resultAtPre = hasRes ? tb.var(variables.result) : tb.NULL();
        final Term resultAtPost =
                hasRes ? buildAfterVar(resultAtPre, "BLOCK", services) : tb.NULL();
        final Term exceptionAtPre = hasExc ? tb.var(variables.exception) : tb.NULL();
        final Term exceptionAtPost =
                hasExc ? buildAfterVar(exceptionAtPre, "BLOCK", services) : tb.NULL();

        // generate proof obligation variables
        final StateVars instantiationPreVars =
                new StateVars(hasSelf ? selfAtPre : null,
                              localVarsAtPre,
                              hasRes ? resultAtPre : null,
                              hasExc ? exceptionAtPre : null,
                              heapAtPre);
        final StateVars instantiationPostVars =
                new StateVars(hasSelf ? selfAtPost : null,
                              localVarsAtPost,
                              hasRes ? resultAtPost : null,
                              hasExc ? exceptionAtPost : null,
                              heapAtPost);
        final ProofObligationVars instantiationVars =
                new ProofObligationVars(instantiationPreVars,
                                        instantiationPostVars,
                                        tb.var(exceptionParameter),
                                        null, tb);
        final IFProofObligationVars ifVars =
                new IFProofObligationVars(instantiationVars, services);
        application.update(ifVars, instantiation.context);

        // generate information flow contract application predicate
        // and associated taclet
        final InfFlowBlockContractTacletBuilder ifContractBuilder =
                new InfFlowBlockContractTacletBuilder(services);
        ifContractBuilder.setContract(contract);
        ifContractBuilder.setExecutionContext(instantiation.context);
        ifContractBuilder.setContextUpdate(); // updates are handled by setUpUsageGoal
        ifContractBuilder.setProofObligationVars(instantiationVars);

        final Term contractApplTerm =
                ifContractBuilder.buildContractApplPredTerm();
        Taclet informationFlowContractApp = ifContractBuilder.buildTaclet();

        // get infFlowAssumptions
        final Term infFlowPreAssumption =
                buildInfFlowPreAssumption(instantiationVars, localOuts,
                                        localOutsAtPre,
                                        tb.var(baseHeap),
                                        tb);
        final Term infFlowPostAssumption =
                buildInfFlowPostAssumption(instantiationVars, localOuts, localOutsAtPost,
                                           tb.var(baseHeap), contractApplTerm, tb);

        // create proof obligation
        InfFlowPOSnippetFactory infFlowFactory =
            POSnippetFactory.getInfFlowFactory(contract, ifVars.c1, ifVars.c2,
                                               instantiation.context, services);

        final SequentFormula poFormula = buildBodyPreservesSequent(infFlowFactory, proof);

        // add proof obligation to goal
        infFlowGoal.addFormula(poFormula, false, true);

        proof.addIFSymbol(contractApplTerm);
        proof.addIFSymbol(informationFlowContractApp);
        proof.addGoalTemplates(informationFlowContractApp);

        return new InfFlowValidityData(infFlowPreAssumption,
                                       infFlowPostAssumption,
                                       informationFlowContractApp);
    }

    private static boolean occursNotAtTopLevelInSuccedent(final PosInOccurrence occurrence) {
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
        contract.setInstantiationSelf(instantiation.self);
        assert contract.getBlock().equals(instantiation.block);
        final Term contextUpdate = instantiation.update;

        final List<LocationVariable> heaps = application.getHeapContext();
        final ImmutableSet<ProgramVariable> localInVariables =
                MiscTools.getLocalIns(instantiation.block, services);
        final ImmutableSet<ProgramVariable> localOutVariables =
                MiscTools.getLocalOuts(instantiation.block, services);
        // final boolean isStrictlyPure = !application.getContract().hasModifiesClause();
        final Map<LocationVariable, Function> anonymisationHeaps =
                createAndRegisterAnonymisationVariables(heaps, contract, services);
        //final Map<LocationVariable, Function> anonymisationLocalVariables = createAndRegisterAnonymisationVariables(localOutVariables, services);

        final BlockContract.Variables variables = new VariablesCreatorAndRegistrar(
            goal, contract.getPlaceholderVariables(), services
        ).createAndRegister(instantiation.self);
        final ProgramVariable exceptionParameter =
                    createLocalVariable("e", variables.exception.getKeYJavaType(),
                                        services);

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

        final UpdatesBuilder updatesBuilder = new UpdatesBuilder(variables, services);
        final Term remembranceUpdate = updatesBuilder.buildRemembranceUpdate(heaps);
        final Term anonymisationUpdate =
                updatesBuilder.buildAnonymisationUpdate(anonymisationHeaps,
                                                        /*anonymisationLocalVariables, */
                                                        modifiesClauses);
        final ImmutableList<Goal> result;
        final GoalsConfigurator configurator = new GoalsConfigurator(instantiation,
                                                                     contract.getLabels(),
                                                                     variables,
                                                                     application.posInOccurrence(),
                                                                     services);
        if (WellDefinednessCheck.isOn()) {
            result = goal.split(4);
            configurator.setUpWdGoal(result.tail().tail().tail().head(),
                                     contract, contextUpdate, heaps.get(0),
                                     anonymisationHeaps.get(heaps.get(0)),
                                     localInVariables);
        } else {
            result = goal.split(3);
        }

        configurator.setUpPreconditionGoal(result.tail().head(),
                                           contextUpdate,
                                           new Term[] {precondition, wellFormedHeapsCondition,
                                                       reachableInCondition});
        configurator.setUpUsageGoal(result.head(),
                                    new Term[] {contextUpdate, remembranceUpdate,
                                                anonymisationUpdate},
                                    new Term[] {postcondition, wellFormedAnonymisationHeapsCondition,
                                                reachableOutCondition, atMostOneFlagSetCondition});
        if (!InfFlowCheckInfo.isInfFlow(goal)) {
            configurator.setUpValidityGoal(result.tail().tail().head(),
                                           new Term[] {contextUpdate, remembranceUpdate},
                                           new Term[] {precondition, wellFormedHeapsCondition,
                                                       reachableInCondition},
                                           new Term[] {postcondition, frameCondition
                                                       /*, atMostOneFlagSetCondition*/},
                                           exceptionParameter);
        } else {
            Goal validityGoal = result.tail().tail().head();
            validityGoal.setBranchLabel("Information Flow Validity");

            // clear goal
            validityGoal.node().setSequent(Sequent.EMPTY_SEQUENT);
            validityGoal.clearAndDetachRuleAppIndex();
            final TermBuilder tb = services.getTermBuilder();

            if (contract.hasModifiesClause(heaps.get(0)) &&
                contract.hasInfFlowSpecs() ) {
                // set up information flow validity goal
                InfFlowValidityData infFlowValidityData =
                    setUpInfFlowValidityGoal(validityGoal, contract,
                                             anonymisationHeaps, services,
                                             variables, exceptionParameter,
                                             heaps, localInVariables,
                                             localOutVariables, application,
                                             instantiation);

                // do additional inf flow preparations on the usage goal
                setUpInfFlowPartOfUsageGoal(result.head(), infFlowValidityData,
                                            contextUpdate, remembranceUpdate,
                                            anonymisationUpdate, tb);
            } else {
                // nothing to prove -> set up trivial goal
                validityGoal.addFormula(new SequentFormula(tb.tt()), false, true);
            }
        }

        return result;
    }

    private Map<LocationVariable, Function>
                createAndRegisterAnonymisationVariables(final Iterable<LocationVariable> variables,
                                                        final BlockContract contract,
                                                        final TermServices services) {
        Map<LocationVariable, Function> result = new LinkedHashMap<LocationVariable, Function>(40);
        final TermBuilder tb = services.getTermBuilder();
        for (LocationVariable variable : variables) {
            if(contract.hasModifiesClause(variable)) {
                final String anonymisationName =
                        tb.newName(ANONYMISATION_PREFIX + variable.name());
                final Function anonymisationFunction =
                        new Function(new Name(anonymisationName), variable.sort(), true);
                services.getNamespaces().functions().addSafely(anonymisationFunction);
                result.put(variable, anonymisationFunction);
            }
        }
        return result;
    }

    @Override
    public BlockContractBuiltInRuleApp createApp(final PosInOccurrence occurrence, TermServices services)
    {
        return new BlockContractBuiltInRuleApp(this, occurrence);
    }

    private ProgramVariable createLocalVariable(final String nameBase,
                                                final KeYJavaType type,
                                                final Services services)
    {
        return KeYJavaASTFactory.localVariable(services.getVariableNamer()
                                .getTemporaryNameProposal(nameBase), type);
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

    static SequentFormula buildBodyPreservesSequent(InfFlowPOSnippetFactory f, Proof proof) {
        Term selfComposedExec =
                f.create(InfFlowPOSnippetFactory.Snippet.SELFCOMPOSED_BLOCK_WITH_PRE_RELATION);
        Term post = f.create(InfFlowPOSnippetFactory.Snippet.INF_FLOW_INPUT_OUTPUT_RELATION);
        final TermBuilder tb = proof.getServices().getTermBuilder();

        final Term finalTerm =
                tb.imp(tb.label(selfComposedExec,
                                ParameterlessTermLabel.SELF_COMPOSITION_LABEL),
                       post);
        proof.addLabeledIFSymbol(selfComposedExec);

        return new SequentFormula(finalTerm);
    }


    private void setUpInfFlowPartOfUsageGoal(final Goal usageGoal,
                                             InfFlowValidityData infFlowValitidyData,
                                             final Term contextUpdate,
                                             final Term remembranceUpdate,
                                             final Term anonymisationUpdate,
                                             final TermBuilder tb) {
        usageGoal.addTaclet(infFlowValitidyData.taclet,
                            SVInstantiations.EMPTY_SVINSTANTIATIONS, true);
        final Term uAssumptions =
                    tb.applySequential(new Term[] {contextUpdate, remembranceUpdate},
                                    tb.and(infFlowValitidyData.preAssumption,
                                           tb.apply(anonymisationUpdate, infFlowValitidyData.postAssumption)));
        usageGoal.addFormula(new SequentFormula(uAssumptions), true, false);
    }


    public static final class Instantiation {

        public final Term update;
        public final Term formula;
        public final Modality modality;
        public final Term self;
        public final StatementBlock block;
        public final ExecutionContext context;

        public Instantiation(final Term update, final Term formula,
                             final Modality modality, final Term self,
                             final StatementBlock block, final ExecutionContext context) {
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

        public Instantiation instantiate()
        {
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

        private Term extractUpdate()
        {
            if (formula.op() instanceof UpdateApplication) {
                return UpdateApplication.getUpdate(formula);
            }
            else {
                return services.getTermBuilder().skip();
            }
        }

        private Term extractUpdateTarget()
        {
            if (formula.op() instanceof UpdateApplication) {
                return UpdateApplication.getTarget(formula);
            }
            else {
                return formula;
            }
        }

        private Term extractSelf(final MethodFrame frame)
        {
            if (frame == null) {
                return null;
            }
            return MiscTools.getSelfTerm(frame, services);
        }

        private static ExecutionContext extractExecutionContext(final MethodFrame frame)
        {
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
                    && !(element instanceof StatementBlock
                            && ((StatementBlock) element).isEmpty())) {
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
        private final TermServices services;

        public VariablesCreatorAndRegistrar(final Goal goal,
                                            final BlockContract.Variables placeholderVariables,
                                            final TermServices services) {
            this.goal = goal;
            this.placeholderVariables = placeholderVariables;
            this.services = services;
        }

        public BlockContract.Variables createAndRegister(Term self)
        {
            return new BlockContract.Variables(
                self != null ? self.op(ProgramVariable.class) : null,
                createAndRegisterFlags(placeholderVariables.breakFlags),
                createAndRegisterFlags(placeholderVariables.continueFlags),
                createAndRegisterVariable(placeholderVariables.returnFlag),
                createAndRegisterVariable(placeholderVariables.result),
                createAndRegisterVariable(placeholderVariables.exception),
                createAndRegisterRemembranceVariables(placeholderVariables.remembranceHeaps),
                createAndRegisterRemembranceVariables(placeholderVariables.remembranceLocalVariables),
                services
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

        private Map<LocationVariable, LocationVariable> createAndRegisterRemembranceVariables(
                final Map<LocationVariable, LocationVariable> remembranceVariables) {
            final Map<LocationVariable, LocationVariable> result =
                    new LinkedHashMap<LocationVariable, LocationVariable>();
            for (Map.Entry<LocationVariable, LocationVariable> remembranceVariable
                    : remembranceVariables.entrySet()) {
                result.put(remembranceVariable.getKey(),
                           createAndRegisterVariable(remembranceVariable.getValue()));
            }
            return result;
        }

        private LocationVariable createAndRegisterVariable(final ProgramVariable placeholderVariable)
        {
            if (placeholderVariable != null) {
                String newName = services.getTermBuilder().newName(placeholderVariable.name().toString());
                LocationVariable newVariable =
                        new LocationVariable(new ProgramElementName(newName),
                                             placeholderVariable.getKeYJavaType());
                goal.addProgramVariable(newVariable);
                return newVariable;
            }
            else {
                return null;
            }
        }

    }

    private static final class UpdatesBuilder extends TermBuilder {

        private final BlockContract.Variables variables;

        public UpdatesBuilder(final BlockContract.Variables variables, final Services services)
        {
            super(services.getTermFactory(), services);
            this.variables = variables;
        }

        public Term buildRemembranceUpdate(final List<LocationVariable> heaps)
        {
            Term result = skip();
            for (LocationVariable heap : heaps) {
                final Term update = elementary(variables.remembranceHeaps.get(heap), var(heap));
                result = parallel(result, update);
            }
            for (Map.Entry<LocationVariable, LocationVariable> remembranceVariable
                    : variables.remembranceLocalVariables.entrySet()) {
                result = parallel(result, elementary(remembranceVariable.getValue(),
                                                     var(remembranceVariable.getKey())));
            }
            return result;
        }

        public Term buildAnonymisationUpdate(final Map<LocationVariable, Function> anonymisationHeaps,
                                             /*final Map<LocationVariable, Function>
                                              *                         anonymisationLocalVariables,*/
                                             final Map<LocationVariable, Term> modifiesClauses) {
            Term result = buildLocalVariablesAnonymisationUpdate(/*anonymisationLocalVariables*/);
            for (Map.Entry<LocationVariable, Function> anonymisationHeap
                    : anonymisationHeaps.entrySet()) {
                Term anonymisationUpdate = skip();
                final Term modifiesClause = modifiesClauses.get(anonymisationHeap.getKey());
                if (!modifiesClause.equals(strictlyNothing())) {
                    anonymisationUpdate = anonUpd(anonymisationHeap.getKey(), modifiesClause,
                          services.getTermBuilder().label(services.getTermBuilder().func(anonymisationHeap.getValue()),
                                                           ParameterlessTermLabel.ANON_HEAP_LABEL));
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
            for (Map.Entry<LocationVariable, Function> anonymisationLocalVariable
                        : anonymisationLocalVariables.entrySet()) {
                result = parallel(result, elementary(anonymisationLocalVariable.getKey(),
                                                     func(anonymisationLocalVariable.getValue())));
            }
            return result;*/
        }

    }

    private static final class ConditionsAndClausesBuilder extends TermBuilder {

        private final BlockContract contract;
        private final List<LocationVariable> heaps;
        private final BlockContract.Variables variables;
        private final BlockContract.Terms terms;

        public ConditionsAndClausesBuilder(final BlockContract contract,
                                           final List<LocationVariable> heaps,
                                           final BlockContract.Variables variables,
                                           final Term self, final Services services) {
            super(services.getTermFactory(), services);
            this.contract = contract;
            this.heaps = heaps;
            this.variables = variables;
            this.terms = variables.termify(self);
        }

        public Term buildPrecondition()
        {
            Term result = tt();
            for (LocationVariable heap : heaps) {
                result = and(result,
                             contract.getPrecondition(heap, getBaseHeap(), terms.self,
                                                      terms.remembranceHeaps, services));
            }
            return result;
        }

        public Term buildWellFormedHeapsCondition()
        {
            Term result = tt();
            for (LocationVariable heap : heaps) {
                result = and(result, wellFormed(heap));
            }
            return result;
        }

        public Term buildReachableInCondition(final ImmutableSet<ProgramVariable> localInVariables)
        {
            return buildReachableCondition(localInVariables);
        }

        public Term buildReachableOutCondition(final ImmutableSet<ProgramVariable> localOutVariables)
        {
            final Term reachableResult =
                    (variables.result != null) ?
                    reachableValue(variables.result) : services.getTermBuilder().tt();
            return and(
                buildReachableCondition(localOutVariables),
                reachableResult,
                reachableValue(variables.exception)
            );
        }

        public Term buildReachableCondition(final ImmutableSet<ProgramVariable> variables)
        {
            Term result = tt();
            for (ProgramVariable variable : variables) {
                result = and(result, reachableValue(variable));
            }
            return result;
        }

        public Map<LocationVariable, Term> buildModifiesClauses()
        {
            Map<LocationVariable, Term> result = new LinkedHashMap<LocationVariable, Term>();
            for (final LocationVariable heap : heaps) {
                result.put(heap, contract.getModifiesClause(heap, var(heap), terms.self, services));
            }
            return result;
        }

        public Term buildPostcondition()
        {
            Term result = tt();
            for (LocationVariable heap : heaps) {
                result = and(result, contract.getPostcondition(heap, getBaseHeap(),
                                                               terms, services));
            }
            return result;
        }

        public Term buildFrameCondition(final Map<LocationVariable, Term> modifiesClauses)
        {
            Term result = tt();
            Map<LocationVariable, Map<Term, Term>> remembranceVariables =
                    constructRemembranceVariables();
            for (LocationVariable heap : heaps) {
                final Term modifiesClause = modifiesClauses.get(heap);
                final Term frameCondition;
                if (modifiesClause.equals(strictlyNothing())) {
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
                result = and(result, wellFormed(services.getTermBuilder().label(services.getTermBuilder().func(anonymisationFunction),
                                                         ParameterlessTermLabel.ANON_HEAP_LABEL)));
            }
            return result;
        }

        public Term buildAtMostOneFlagSetCondition()
        {
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

        private List<Term> buildFlagsNotSetConditions(final Collection<ProgramVariable> flags)
        {
            final List<Term> result = new LinkedList<Term>();
            for (ProgramVariable flag : flags) {
                result.add(buildFlagNotSetCondition(flag));
            }
            return result;
        }

        private Term buildFlagNotSetCondition(final ProgramVariable flag)
        {
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

        public void setUpWdGoal(final Goal goal, final BlockContract contract,
                                final Term update, final LocationVariable heap,
                                final Function anonHeap,
                                final ImmutableSet<ProgramVariable> localIns) {
            if (goal == null) {
                return;
            }
            goal.setBranchLabel(WellDefinednessMacro.WD_BRANCH);
            final BlockWellDefinedness bwd = new BlockWellDefinedness(contract, localIns, services);
            services.getSpecificationRepository().addWdStatement(bwd);
            final LocationVariable heapAtPre = variables.remembranceHeaps.get(heap);
            final Term anon = anonHeap != null ? services.getTermBuilder().func(anonHeap) : null;
            final SequentFormula wdBlock = bwd.generateSequent(variables.self, variables.exception,
                    variables.result, heap, heapAtPre,
                    anon, localIns, update, services);
            goal.changeFormula(wdBlock, occurrence);
        }

        public void setUpValidityGoal(final Goal goal, final Term[] updates,
                                      final Term[] assumptions,
                                      final Term[] postconditions,
                                      final ProgramVariable exceptionParameter) {
            goal.setBranchLabel("Validity");
            final TermBuilder tb = services.getTermBuilder();
            goal.addFormula(new SequentFormula(
                    tb.applySequential(updates, tb.and(assumptions))), true, false);
            final StatementBlock block =
                    new ValidityProgramConstructor(labels, instantiation.block,
                                                   variables, exceptionParameter,
                                                   services).construct();
            Statement wrappedBlock = wrapInMethodFrameIfContextIsAvailable(block);
            StatementBlock finishedBlock = finishTransactionIfModalityIsTransactional(wrappedBlock);
            goal.changeFormula(new SequentFormula(
                  tb.applySequential(
                    updates,
                    tb.prog(instantiation.modality,
                            JavaBlock.createJavaBlock(finishedBlock), tb.and(postconditions)))),
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
                return new StatementBlock(statement, new TransactionStatement(
                        de.uka.ilkd.key.java.recoderext.TransactionStatement.FINISH));
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
            final TermBuilder tb = services.getTermBuilder();
            goal.setBranchLabel("Precondition");
            goal.changeFormula(new SequentFormula(tb.apply(update, tb.and(preconditions), null)),
                               occurrence);
        }

        public void setUpUsageGoal(final Goal goal, final Term[] updates,
                                   final Term[] assumptions) {
            final TermBuilder tb = services.getTermBuilder();
            goal.setBranchLabel("Usage");
            Term uAssumptions = tb.applySequential(updates, tb.and(assumptions));
            goal.addFormula(new SequentFormula(uAssumptions), true, false);
            goal.changeFormula(new SequentFormula(tb.applySequential(updates, buildUsageFormula())),
                                                  occurrence);
        }

        private Term buildUsageFormula()
        {
            return services.getTermBuilder().prog(
                instantiation.modality,
                replaceBlock(instantiation.formula.javaBlock(), instantiation.block,
                             constructAbruptTerminationIfCascade()),
                instantiation.formula.sub(0)
            );
        }

        private JavaBlock replaceBlock(final JavaBlock java, final StatementBlock oldBlock,
                                       final StatementBlock newBlock) {
            Statement newProgram = (Statement) new ProgramElementReplacer(java.program(), services)
                                                                       .replace(oldBlock, newBlock);
            return JavaBlock.createJavaBlock(newProgram instanceof StatementBlock ?
                    (StatementBlock) newProgram : new StatementBlock(newProgram));
        }

        private StatementBlock constructAbruptTerminationIfCascade() {
            List<If> ifCascade = new ArrayList<If>();
            for (Map.Entry<Label, ProgramVariable> flag : variables.breakFlags.entrySet()) {
                ifCascade.add(KeYJavaASTFactory.ifThen(flag.getValue(),
                        KeYJavaASTFactory.breakStatement(flag.getKey())));
            }
            for (Map.Entry<Label, ProgramVariable> flag : variables.continueFlags.entrySet()) {
                ifCascade.add(KeYJavaASTFactory.ifThen(flag.getValue(),
                        KeYJavaASTFactory.continueStatement(flag.getKey())));
            }
            if (variables.returnFlag != null) {
                ifCascade.add(KeYJavaASTFactory.ifThen(variables.returnFlag,
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
        private final ProgramVariable exceptionParameter;

        public ValidityProgramConstructor(final Iterable<Label> labels,
                                          final StatementBlock block,
                                          final BlockContract.Variables variables,
                                          final ProgramVariable exceptionParameter,
                                          final Services services) {
            this.labels = labels;
            this.block = block;
            this.variables = variables;
            this.services = services;
            this.exceptionParameter = exceptionParameter;
            statements = new LinkedList<Statement>();
        }

        public StatementBlock construct()
        {
            declareFlagsFalse();
            declareResultDefault();
            declareExceptionNull();
            executeBlockSafely();
            return new StatementBlock(statements.toArray(new Statement[statements.size()]));
        }

        private void declareFlagsFalse()
        {
            declareFlagsFalse(variables.breakFlags.values());
            declareFlagsFalse(variables.continueFlags.values());
            if (variables.returnFlag != null) {
                declareFlagFalse(variables.returnFlag);
            }
        }

        private void declareFlagsFalse(final Collection<ProgramVariable> flags)
        {
            for (ProgramVariable flag : flags) {
                declareFlagFalse(flag);
            }
        }

        private void declareFlagFalse(final ProgramVariable flag) {
            statements.add(KeYJavaASTFactory.declare(flag, BooleanLiteral.FALSE,
                             services.getJavaInfo().getKeYJavaType("boolean")));
        }

        private void declareResultDefault() {
            if (occursReturnAndIsReturnTypeNotVoid()) {
                KeYJavaType resultType = variables.result.getKeYJavaType();
                statements.add(KeYJavaASTFactory.declare(
                        variables.result, resultType.getDefaultValue(), resultType));
            }
        }

        private boolean occursReturnAndIsReturnTypeNotVoid() {
            return variables.returnFlag != null && variables.result != null;
        }

        private void declareExceptionNull() {
            statements.add(KeYJavaASTFactory.declare(
                    variables.exception, NullLiteral.NULL, variables.exception.getKeYJavaType()));
        }

        private void executeBlockSafely() {
            final Label breakOutLabel = new ProgramElementName("breakOut");
            final StatementBlock almostSafeBlock =
                    replaceOuterBreaksContinuesAndReturns(block, breakOutLabel);
            final Statement labeledAlmostSafeBlock = label(almostSafeBlock, labels);
            final Statement safeStatement = wrapInTryCatch(labeledAlmostSafeBlock,
                                                           exceptionParameter);
            statements.add(new LabeledStatement(breakOutLabel, safeStatement));
        }

        private Statement label(final StatementBlock block, Iterable<Label> labels)
        {
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
                variables.returnFlag, variables.result, services
            ).replace();
        }

        private Statement wrapInTryCatch(final Statement labeldBlock,
                                         final ProgramVariable exceptionParameter) {
            Catch katch =
                    KeYJavaASTFactory.catchClause(KeYJavaASTFactory.parameterDeclaration(
                                                                    services.getJavaInfo(),
                                                                    exceptionParameter.getKeYJavaType(),
                                                                    exceptionParameter),
                                                  new StatementBlock(KeYJavaASTFactory.assign(
                                                          variables.exception, exceptionParameter)));
            return new Try(new StatementBlock(labeldBlock), new Branch[] {katch});
        }
    }

    private class InfFlowValidityData {
        final Term preAssumption;
        final Term postAssumption;
        final Taclet taclet;

        public InfFlowValidityData(final Term preAssumption,
                                   final Term postAssumption,
                                   final Taclet taclet) {
            this.preAssumption = preAssumption;
            this.postAssumption = postAssumption;
            this.taclet = taclet;
        }
    }
}
