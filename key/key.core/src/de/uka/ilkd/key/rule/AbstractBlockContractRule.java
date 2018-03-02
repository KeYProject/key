package de.uka.ilkd.key.rule;

import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;
import org.key_project.util.collection.ImmutableSet;

import de.uka.ilkd.key.informationflow.po.BlockExecutionPO;
import de.uka.ilkd.key.informationflow.po.IFProofObligationVars;
import de.uka.ilkd.key.informationflow.po.SymbolicExecutionPO;
import de.uka.ilkd.key.informationflow.po.snippet.InfFlowPOSnippetFactory;
import de.uka.ilkd.key.informationflow.po.snippet.POSnippetFactory;
import de.uka.ilkd.key.informationflow.proof.InfFlowCheckInfo;
import de.uka.ilkd.key.informationflow.proof.InfFlowProof;
import de.uka.ilkd.key.informationflow.proof.init.StateVars;
import de.uka.ilkd.key.informationflow.rule.tacletbuilder.InfFlowBlockContractTacletBuilder;
import de.uka.ilkd.key.java.JavaTools;
import de.uka.ilkd.key.java.KeYJavaASTFactory;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.StatementContainer;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.statement.CatchAllStatement;
import de.uka.ilkd.key.java.statement.MethodFrame;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.ProgramPrefix;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.label.ParameterlessTermLabel;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.Transformer;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.proof.init.ProofObligationVars;
import de.uka.ilkd.key.proof.mgt.SpecificationRepository;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.speclang.BlockContract;
import de.uka.ilkd.key.speclang.BlockSpecificationElement;
import de.uka.ilkd.key.util.MiscTools;

public abstract class AbstractBlockContractRule implements BuiltInRule  {
    
    public static final String FULL_PRECONDITION_TERM_HINT = "fullPrecondition";
    public static final String NEW_POSTCONDITION_TERM_HINT = "newPostcondition";

    protected static boolean occursNotAtTopLevelInSuccedent(final PosInOccurrence occurrence) {
        return occurrence == null || !occurrence.isTopLevel() || occurrence.isInAntec();
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

    public static ImmutableSet<BlockContract>
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

    /**
     * Adds {@code pv} to the {@code sevices}' program variable namespace.
     * 
     * @param pv
     * @param services
     */
    protected static void register(ProgramVariable pv,
                         Services services) {
        Namespace<IProgramVariable> progVarNames = services.getNamespaces().programVariables();
        if (pv != null && progVarNames.lookup(pv.name()) == null) {
            progVarNames.addSafely(pv);
        }
    }

    protected static ImmutableSet<BlockContract>
                        filterAppliedContracts(final ImmutableSet<BlockContract> collectedContracts,
                                               final Goal goal) {
        ImmutableSet<BlockContract> result = DefaultImmutableSet.<BlockContract>nil();
        for (BlockContract contract : collectedContracts) {
            if (!contractApplied(contract, goal) ||
                    InfFlowCheckInfo.isInfFlow(goal)) {
                result = result.add(contract);
            }
        }
        return result;
    }

    // This seems to be inefficient...
    protected static boolean contractApplied(final BlockContract contract,
                                           final Goal goal) {
        Node selfOrParentNode = goal.node();
        Node previousNode = null;
        while (selfOrParentNode != null) {
            RuleApp app = selfOrParentNode.getAppliedRuleApp();
            if (app instanceof BlockContractInternalBuiltInRuleApp) {
                BlockContractInternalBuiltInRuleApp blockRuleApp =
                        (BlockContractInternalBuiltInRuleApp)app;
                if (blockRuleApp.getBlock().equals(contract.getBlock()) && 
                        selfOrParentNode.getChildNr(previousNode) == 0) {
                    // prevent application of contract in its own check validity branch
                    // but not in other branches, e.g., do-while 
                    // loops might need to apply the same contract 
                    // twice in its usage branch
                    return true;
                }
            }
            previousNode = selfOrParentNode;
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

    public abstract Instantiation getLastInstantiation();
    public abstract Term getLastFocusTerm();

    protected abstract void setLastInstantiation(Instantiation result);
    protected abstract void setLastFocusTerm(Term formula);

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

    @Override
    public String displayName()
    {
        return name().toString();
    }

    @Override
    public String toString()
    {
        return name().toString();
    }
    
    @Override
    public boolean isApplicableOnSubTerms() {
       return false;
    }

    public Instantiation instantiate(final Term formula,
                                     final Goal goal,
                                     final Services services) {
        if (formula == getLastFocusTerm()) {
            return getLastInstantiation();
        } else {
            final Instantiation result =
                    new Instantiator(formula, goal, services).instantiate();
            setLastFocusTerm(formula);
            setLastInstantiation(result);
            return result;
        }
    }
    
    protected Map<LocationVariable, Function>
                createAndRegisterAnonymisationVariables(final Iterable<LocationVariable> variables,
                                                        final BlockContract contract,
                                                        final TermServices services) {
        Map<LocationVariable, Function> result = new LinkedHashMap<LocationVariable, Function>(40);
        final TermBuilder tb = services.getTermBuilder();
        for (LocationVariable variable : variables) {
            if(contract.hasModifiesClause(variable)) {
                final String anonymisationName =
                        tb.newName(BlockContractBuilders.ANON_OUT_PREFIX + variable.name());
                final Function anonymisationFunction =
                        new Function(new Name(anonymisationName), variable.sort(), true);
                services.getNamespaces().functions().addSafely(anonymisationFunction);
                result.put(variable, anonymisationFunction);
            }
        }
        return result;
    }

    protected static Term createLocalAnonUpdate(ImmutableSet<ProgramVariable> localOuts,
                                              Services services) {
        Term anonUpdate = null;
        final TermBuilder tb = services.getTermBuilder();
        for(ProgramVariable pv : localOuts) {
            final Name anonFuncName = new Name(tb.newName(pv.name().toString()));
            final Function anonFunc = new Function(anonFuncName, pv.sort(), true);
            services.getNamespaces().functions().addSafely(anonFunc);
            final Term elemUpd = tb.elementary((LocationVariable)pv, tb.func(anonFunc));
            if(anonUpdate == null) {
                anonUpdate = elemUpd;
            } else {
                anonUpdate = tb.parallel(anonUpdate, elemUpd);
            }
        }
        
        return anonUpdate == null
                ? services.getTermBuilder().skip()
                : anonUpdate;
    }

    protected static ProgramVariable createLocalVariable(final String nameBase,
                                                final KeYJavaType type,
                                                final Services services) {
        return KeYJavaASTFactory.localVariable(services.getVariableNamer()
                                .getTemporaryNameProposal(nameBase), type);
    }
    
    /*
     * Factory methods for information flow contracts.
     * 
     * TODO These could be moved into a separate class (like BlockContractBuilders)
     * to allow them to be reused in other classes.
     */

    protected static Term buildAfterVar(Term varTerm,
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

    protected static ImmutableList<Term> buildLocalOutsAtPre(ImmutableList<Term> varTerms,
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

    protected static ImmutableList<Term> buildLocalOutsAtPost(ImmutableList<Term> varTerms,
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

    protected static Term buildInfFlowPreAssumption(ProofObligationVars instVars,
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

    protected static Term buildInfFlowPostAssumption(ProofObligationVars instVars,
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

    static SequentFormula buildBodyPreservesSequent(InfFlowPOSnippetFactory f, InfFlowProof proof) {
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

    protected void setUpInfFlowPartOfUsageGoal(final Goal usageGoal,
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
    
    protected InfFlowValidityData
                setUpInfFlowValidityGoal(final Goal infFlowGoal,
                                         final BlockContract contract,
                                         final Map<LocationVariable, Function> anonymisationHeaps,
                                         final Services services,
                                         final BlockSpecificationElement.Variables variables,
                                         final ProgramVariable exceptionParameter,
                                         final List<LocationVariable> heaps,
                                         final ImmutableSet<ProgramVariable> localInVariables,
                                         final ImmutableSet<ProgramVariable> localOutVariables,
                                         final BlockContractInternalBuiltInRuleApp application,
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
        
        assert infFlowGoal.proof() instanceof InfFlowProof;
        final InfFlowProof proof = (InfFlowProof) infFlowGoal.proof();

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

    protected static class InfFlowValidityData {
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

        public boolean isTransactional() {
            return modality.transaction();
        }

    }

    protected static final class Instantiator {

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
                return services.getTermBuilder().skip();
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

        private static ExecutionContext extractExecutionContext(final MethodFrame frame) {
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

    public static class BlockContractHint {
        protected final static BlockContractHint USAGE_BRANCH = new BlockContractHint("Usage Branch");
        
        private final ProgramVariable excVar;

        private final String description;

        public BlockContractHint(String description, ProgramVariable excVar) {
            this.description = description;
            this.excVar = excVar;
        }

        public static BlockContractHint createUsageBranchHint() {
            return USAGE_BRANCH;
        }

        public static BlockContractHint createValidityBranchHint(ProgramVariable excVar) {
            return new BlockContractHint("Validity Branch", excVar);
        }



        public BlockContractHint(String description) {
            this.description = description;
            this.excVar = null;
        }

        public ProgramVariable getExceptionalVariable() {
            return excVar;
        }

        public String getDescription() {
            return description;
        }


        @Override
        public String toString() {
            return description + (excVar != null ? "Validity Branch: exceptionVar=" + excVar.name() : "");

        }
    }
}
