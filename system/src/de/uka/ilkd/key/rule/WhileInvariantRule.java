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

import de.uka.ilkd.key.rule.tacletbuilder.InfFlowLoopInvariantTacletBuilder;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.JavaTools;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.Statement;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.LocalVariableDeclaration;
import de.uka.ilkd.key.java.declaration.VariableSpecification;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.reference.TypeRef;
import de.uka.ilkd.key.java.statement.MethodFrame;
import de.uka.ilkd.key.java.statement.While;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.logic.label.AnonHeapTermLabel;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.label.SelfCompositionTermLabel;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.ProgramSV;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.InfFlowCheckInfo;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.IFProofObligationVars;
import de.uka.ilkd.key.proof.init.InfFlowPO;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.proof.init.StateVars;
import de.uka.ilkd.key.proof.init.ProofObligationVars;
import de.uka.ilkd.key.proof.init.po.snippet.InfFlowPOSnippetFactory;
import de.uka.ilkd.key.proof.init.po.snippet.POSnippetFactory;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.rule.label.TermLabelWorkerManagement;
import de.uka.ilkd.key.rule.metaconstruct.WhileInvariantTransformer;
import de.uka.ilkd.key.speclang.LoopInvariant;
import de.uka.ilkd.key.strategy.StrategyProperties;
import de.uka.ilkd.key.util.MiscTools;
import de.uka.ilkd.key.util.Pair;
import de.uka.ilkd.key.util.properties.Properties.Property;

public final class WhileInvariantRule implements BuiltInRule {


    public static final WhileInvariantRule INSTANCE = new WhileInvariantRule();

    private static final Name NAME = new Name("Use Loop Invariant");
    private static final TermBuilder TB = TermBuilder.DF;

    private static Term lastFocusTerm;
    private static Instantiation lastInstantiation;


    private static InfFlowData prepareSetUpOfInfFlowValidityGoal(final AnonUpdateData anonUpdateData,
                                                                 final LocationVariable guardVar,
                                                                 final Instantiation inst,
                                                                 LoopInvariant inv,
                                                                 Services services,
                                                                 LoopInvariantBuiltInRuleApp ruleApp,
                                                                 final ImmutableSet<ProgramVariable> localIns,
                                                                 final ImmutableSet<ProgramVariable> localOuts,
                                                                 final Term anonUpdate,
                                                                 final JavaBlock guardJb)
            throws RuleAbortException {
        final Term baseHeap = anonUpdateData.loopHeapAtPre;
        final Term guardTerm = TB.var(guardVar);
        final Term selfTerm = inst.selfTerm;

        Proof proof = services.getProof();
        ProofOblInput poi =
                services.getSpecificationRepository().getProofOblInput(proof);
        assert poi instanceof InfFlowPO;
        InfFlowPO po = (InfFlowPO)poi;
        IFProofObligationVars leaveIFVars = po.getLeaveIFVars();

        services.getSpecificationRepository().addLoopInvariant(inv);
        ruleApp.setLoopInvariant(inv);
        instantiate(ruleApp, services);

        // create heap_Before_LOOP
        HeapLDT heapLDT = services.getTypeConverter().getHeapLDT();
        Name heapAtPreName = new Name(TB.newName(services, baseHeap + "_Before_LOOP"));
        final Function heapAtPreFunc = new Function(heapAtPreName, heapLDT.targetSort(), true);
	services.getNamespaces().functions().addSafely(heapAtPreFunc);
        final Term heapAtPre = TB.func(heapAtPreFunc);

        final Term heapAtPost = anonUpdateData.loopHeap;
        final Term guardAtPre = buildBeforeVar(guardTerm, services);
        final Term guardAtPost = buildAfterVar(guardTerm, services);
        final Term selfAtPost = buildAtPostVar(selfTerm, "LOOP", services);
        // The set of local variables which are read in the loop body.
        final ImmutableList<Term> localInTerms = MiscTools.toTermList(localIns);
        // The set of local vairables which are written in the loop body.
        final ImmutableList<Term> localOutTerms = MiscTools.toTermList(localOuts);
        // For every local variable which is written we need a pre and a post varible.
        final ImmutableList<Term> localOutsAtPre = buildLocalOutsAtPre(localOutTerms, services);
        final ImmutableList<Term> localOutsAtPost = buildLocalOutsAtPost(localOutTerms, services);
        // For every local variable which is read only, we need only a pre
        // variable (because the value of those variables does not change).
        // localIns contains the local variables which might be read in the
        // loop body, localOuts contains the local variables which might be
        // assigned. Both sets might overlap. Because we already generated
        // pre and post variables for all variables which might be assigned to,
        // additional pre variables need to be generated only for those variables
        // which are contained in localInTerms but not in localOutTerms.
        // Hence we have to filter out those local variables from localIns which
        // also appear in localOuts.
        final ImmutableList<Term> localInsWithoutOutDuplicates =
                MiscTools.filterOutDuplicates(localInTerms, localOutTerms);
        // The set of local pre variables is the union of the pre variables
        // generated for the variables which are assigned to and the pre
        // variables for the variables which are read only.
        final ImmutableList<Term> localVarsAtPre =
                localInsWithoutOutDuplicates.append(localOutsAtPre);
        // The set of local post variables is the union of the post variables
        // generated for the variables which are assigned to and the pre
        // variables for the variables which are read only.
        final ImmutableList<Term> localVarsAtPost =
                localInsWithoutOutDuplicates.append(localOutsAtPost);

        // generate proof obligation variables
        final StateVars instantiationPreVars =
                new StateVars(selfTerm, guardAtPre, localVarsAtPre, heapAtPre);
        final StateVars instantiationPostVars =
                new StateVars(selfAtPost, guardAtPost, localVarsAtPost, heapAtPost);
        final ProofObligationVars instantiationVars =
                new ProofObligationVars(instantiationPreVars,
                                        instantiationPostVars,
                                        services);

        // generate information flow invariant application predicate
        // and associated taclet
        final Pair<Term, Term> updates = new Pair<Term, Term> (inst.u, anonUpdate);
        final InfFlowLoopInvariantTacletBuilder ifInvariantBuilder =
                new InfFlowLoopInvariantTacletBuilder(services);
        ifInvariantBuilder.setInvariant(inv);
        ifInvariantBuilder.setExecutionContext(inst.innermostExecutionContext);
        ifInvariantBuilder.setContextUpdate(/*inst.u*/);
        ifInvariantBuilder.setProofObligationVars(instantiationVars);
        ifInvariantBuilder.setGuard(guardTerm);

        final Term loopInvApplPredTerm =
                ifInvariantBuilder.buildContractApplPredTerm();
        final Taclet informationFlowInvariantApp =
                ifInvariantBuilder.buildTaclet();

        // return information flow data
        InfFlowData infFlowData = new InfFlowData(instantiationVars, guardAtPre,
                                                  guardAtPost, guardJb,
                                                  guardTerm, localOutTerms,
                                                  localOutsAtPre, localOutsAtPost,
                                                  updates, loopInvApplPredTerm,
                                                  informationFlowInvariantApp);
        return infFlowData;
    }


    //-------------------------------------------------------------------------
    //constructors
    //-------------------------------------------------------------------------

    private WhileInvariantRule() {
    }


    //-------------------------------------------------------------------------
    //internal methods
    //-------------------------------------------------------------------------

    private static Instantiation instantiate(final LoopInvariantBuiltInRuleApp app,
                                             Services services) throws RuleAbortException {
    final Term focusTerm = app.posInOccurrence().subTerm();

    if(focusTerm == lastFocusTerm &&
            lastInstantiation.inv == services.getSpecificationRepository()
                                        .getLoopInvariant(lastInstantiation.loop)) {
	    return lastInstantiation;
	}

	//leading update?
	final Pair<Term, Term> update = applyUpdates(focusTerm);
	final Term u        = update.first;
	final Term progPost = update.second;

	//focus (below update) must be modality term
	if (!checkFocus(progPost)) {
	    return null;
	}

	//active statement must be while loop
	final While loop = (While) app.getLoopStatement();

	// try to get invariant from JML specification
	LoopInvariant inv = app.getInvariant();
	assert inv != null : "No invariant found"; // FIXME: Remove after debugging
	if (inv == null) // may happen after reloading proof 
	    throw new RuleAbortException("no invariant found");

	//collect self, execution context
	final MethodFrame innermostMethodFrame =
	        JavaTools.getInnermostMethodFrame(progPost.javaBlock(), services);
	inv = inv.setTarget(innermostMethodFrame.getProgramMethod());

	final Term selfTerm = innermostMethodFrame == null
	                      ? null
	                      : MiscTools.getSelfTerm(innermostMethodFrame, services);

	final ExecutionContext innermostExecutionContext =
	        innermostMethodFrame == null
	        ? null
	        : (ExecutionContext) innermostMethodFrame.getExecutionContext();
	inv = inv.setExecutionContext(innermostExecutionContext);
	services.getSpecificationRepository().addLoopInvariant(inv);

	//cache and return result
	final Instantiation result = new Instantiation(u, progPost, loop, inv, selfTerm,
	                                               innermostExecutionContext);
	lastFocusTerm = focusTerm;
	lastInstantiation = result;
	return result;
    }


    private static Term createLocalAnonUpdate(ImmutableSet<ProgramVariable> localOuts,
                                              Services services) {
        Term anonUpdate = null;
        for(ProgramVariable pv : localOuts) {
            final Name anonFuncName = new Name(TB.newName(services, pv.name().toString()));
            final Function anonFunc = new Function(anonFuncName, pv.sort(), true);
            services.getNamespaces().functions().addSafely(anonFunc);
            final Term elemUpd = TB.elementary(services, (LocationVariable)pv, TB.func(anonFunc));
            if(anonUpdate == null) {
                anonUpdate = elemUpd;
            } else {
                anonUpdate = TB.parallel(anonUpdate, elemUpd);
            }
        }

        return anonUpdate;
    }

    /**
     * @return (assumption, anon update, anon heap)
     */    
    private static AnonUpdateData createAnonUpdate(LocationVariable heap, Term mod,
                                                   LoopInvariant inv, Services services) {
	final HeapLDT heapLDT = services.getTypeConverter().getHeapLDT();
	final Name loopHeapName = new Name(TB.newName(services, heap+"_After_LOOP"));
	final Function loopHeapFunc = new Function(loopHeapName, heapLDT.targetSort(), true);
	services.getNamespaces().functions().addSafely(loopHeapFunc);

        final Term loopHeap = TB.func(loopHeapFunc);
	final Name anonHeapName = new Name(TB.newName(services, "anon_"+heap+"_LOOP"));
	final Function anonHeapFunc = new Function(anonHeapName,heap.sort(), true);
	services.getNamespaces().functions().addSafely(anonHeapFunc);
        final Term anonHeapTerm = TB.label(TB.func(anonHeapFunc), AnonHeapTermLabel.INSTANCE);

	// check for strictly pure loops
	final Term anonUpdate;
	if(TB.strictlyNothing().equals(mod)) {
	    anonUpdate = TB.skip();
	} else {
	    anonUpdate = TB.anonUpd(heap, services, mod, anonHeapTerm);
	}

	return new AnonUpdateData(anonUpdate, loopHeap, TB.getBaseHeap(services), anonHeapTerm);
    }

    private static boolean checkFocus(final Term progPost) {
        // focus (below update) must be modality term
        return progPost.op() instanceof Modality;
    }

    private static Term buildAtPostVar(Term varTerm,
                                       String suffix,
                                       Services services) {
        if (varTerm == null) {
            return null;
        }
        assert varTerm.op() instanceof LocationVariable;

        final KeYJavaType resultType = ((LocationVariable)varTerm.op()).getKeYJavaType();
        if (!suffix.equalsIgnoreCase("")) {
            suffix = new String("_" + suffix);
        }
        final String name = TermBuilder.DF.newName(services, varTerm.toString() + "_After" + suffix);
        final LocationVariable varAtPostVar =
                new LocationVariable(new ProgramElementName(name), resultType);
        register(varAtPostVar, services);
        final Term varAtPost = TermBuilder.DF.var(varAtPostVar);
        return varAtPost;
    }

    private static Term buildBeforeVar(Term varTerm,
                                       Services services) {
        if (varTerm == null) {
            return null;
        }
        assert varTerm.op() instanceof LocationVariable;        

        final KeYJavaType resultType = ((LocationVariable)varTerm.op()).getKeYJavaType();
        final String name = TermBuilder.DF.newName(services, varTerm.toString() + "_Before");
        final LocationVariable varAtPreVar =
                new LocationVariable(new ProgramElementName(name), resultType);
        register(varAtPreVar, services);
        final Term varAtPre = TermBuilder.DF.var(varAtPreVar);
        return varAtPre;
    }

    private static Term buildAfterVar(Term varTerm,
                                      Services services) {
        if (varTerm == null) {
            return null;
        }
        assert varTerm.op() instanceof LocationVariable;        

        final KeYJavaType resultType = ((LocationVariable)varTerm.op()).getKeYJavaType();
        final String name = TermBuilder.DF.newName(services, varTerm.toString() + "_After");
        final LocationVariable varAtPostVar =
                new LocationVariable(new ProgramElementName(name), resultType);
        register(varAtPostVar, services);
        final Term varAtPost = TermBuilder.DF.var(varAtPostVar);
        return varAtPost;
    }

    private static ImmutableList<Term> buildLocalOutsAtPre(ImmutableList<Term> varTerms,
                                                           Services services) {
        if (varTerms == null || varTerms.isEmpty()) {
            return varTerms;
        }
        ImmutableList<Term> localOuts = ImmutableSLList.<Term>nil();
        for(final Term varTerm: varTerms) {
            assert varTerm.op() instanceof LocationVariable;

            final KeYJavaType resultType = ((LocationVariable)varTerm.op()).getKeYJavaType();

            final String name = TermBuilder.DF.newName(services, varTerm.toString() + "_Before");
            final LocationVariable varAtPostVar =
                    new LocationVariable(new ProgramElementName(name), resultType);
            register(varAtPostVar, services);
            final Term varAtPost = TermBuilder.DF.var(varAtPostVar);
            localOuts = localOuts.append(varAtPost);
        }
        return localOuts;
    }

    private static ImmutableList<Term> buildLocalOutsAtPost(ImmutableList<Term> varTerms,
                                                            Services services) {
        if (varTerms == null || varTerms.isEmpty()) {
            return varTerms;
        }
        ImmutableList<Term> localOuts = ImmutableSLList.<Term>nil();
        for(final Term varTerm: varTerms) {
            assert varTerm.op() instanceof LocationVariable;

            final KeYJavaType resultType = ((LocationVariable)varTerm.op()).getKeYJavaType();

            final String name = TermBuilder.DF.newName(services, varTerm.toString() + "_After");
            final LocationVariable varAtPostVar =
                    new LocationVariable(new ProgramElementName(name), resultType);
            register(varAtPostVar, services);
            final Term varAtPost = TermBuilder.DF.var(varAtPostVar);
            localOuts = localOuts.append(varAtPost);
        }
        return localOuts;
    }

    static void register(ProgramVariable pv,
                         Services services) {
        final Namespace progVarNames = services.getNamespaces().programVariables();
        if (pv != null && progVarNames.lookup(pv.name()) == null) {
            progVarNames.addSafely(pv);
        }
    }

    private static void setUpInfFlowPartOfUseGoal(final InfFlowData infData,
                                                       final Term baseHeap,
                                                       Goal goal) {
        assert infData != null;
        final ProofObligationVars symbExecVars = infData.symbExecVars;
        final Term heapAtPreEq =
                TB.equals(symbExecVars.pre.heap, baseHeap);
        final Term heapAtPostEq =
                TB.equals(symbExecVars.post.heap, baseHeap);
        Term beforeAssumptions = TB.and(heapAtPreEq,
                                        TB.box(infData.guardJb,
                                               TB.equals(infData.guardAtPre,
                                                         infData.guardTerm)));
        Iterator<Term> outsAtPre = infData.localOutsAtPre.iterator();
        for (Term locOut: infData.localOuts) {
            beforeAssumptions = TB.and(beforeAssumptions, TB.equals(outsAtPre.next(), locOut));
        }

        Term selfAtPostAssumption =
                // if the method is not static and if it is no constructor
                (symbExecVars.pre.self != null && symbExecVars.post.self != null) ?
                // then the self-variable does not change
                TB.equals(symbExecVars.post.self, symbExecVars.pre.self) :
                // else there is nothing to say about self
                TB.tt();
        Term afterAssumptions = TB.and(heapAtPostEq,
                                       TB.box(infData.guardJb,
                                              TB.equals(infData.guardAtPost,
                                                        infData.guardTerm)),
                                       selfAtPostAssumption);
        final Iterator<Term> outsAtPost = infData.localOutsAtPost.iterator();
        for (final Term locOut: infData.localOuts) {
            afterAssumptions = TB.and(afterAssumptions, TB.equals(outsAtPost.next(), locOut));
        }

        final Term infFlowAssumptions =
                TB.apply(infData.updates.first,
                         TB.and(beforeAssumptions,
                                TB.apply(infData.updates.second,
                                         TB.and(afterAssumptions, infData.applPredTerm))));

        goal.addFormula(new SequentFormula(infFlowAssumptions),
                        true,
                        false);
        goal.addTaclet(infData.infFlowApp,
                       SVInstantiations.EMPTY_SVINSTANTIATIONS, true);
        goal.proof().addIFSymbol(infData.applPredTerm);
        goal.proof().addIFSymbol(infData.infFlowApp);
        goal.proof().addGoalTemplates(infData.infFlowApp);
    }

    private static boolean isInfFlow(Goal goal) {
        StrategyProperties stratProps =
                goal.proof().getSettings().getStrategySettings().getActiveStrategyProperties();
        Property<Boolean> ifProp = InfFlowCheckInfo.INF_FLOW_CHECK_PROPERTY;
        String ifStrat = StrategyProperties.INF_FLOW_CHECK_PROPERTY;
        String ifTrue = StrategyProperties.INF_FLOW_CHECK_TRUE;

        boolean isOriginalIF =
                (goal.getStrategyInfo(ifProp) != null && goal.getStrategyInfo(ifProp));
        // For loaded proofs, InfFlowCheckInfo is not correct without the following
        boolean isLoadedIF = false; //stratProps.getProperty(ifStrat).equals(ifTrue);
        return isOriginalIF || isLoadedIF;
    }

    private static InfFlowData setUpInfFlowValidityGoal(Goal infFlowGoal,
                                                        LoopInvariantBuiltInRuleApp ruleApp,
                                                        final Instantiation inst,
                                                        final LocationVariable guardVar,
                                                        final JavaBlock guardJb,
                                                        final ImmutableSet<ProgramVariable> localIns,
                                                        final ImmutableSet<ProgramVariable> localOuts,
                                                        final ImmutableList<AnonUpdateData> anonUpdateDatas,
                                                        final Term anonUpdate,
                                                        Services services)
            throws RuleAbortException {
        assert anonUpdateDatas.size() == 1 : "information flow " +
                                             "extension is at the " +
                                             "moment not compatible " +
                                             "with the non-base-heap " +
                                             "setting";
        final AnonUpdateData anonUpdateData = anonUpdateDatas.head();

        // prepare data
        LoopInvariant inv = inst.inv;
        InfFlowData infFlowData =
                prepareSetUpOfInfFlowValidityGoal(anonUpdateData, guardVar,
                                                  inst, inv, services, ruleApp,
                                                  localIns, localOuts,
                                                  anonUpdate, guardJb);

        // generate information flow proof obligation variables
        final IFProofObligationVars ifVars =
                new IFProofObligationVars(infFlowData.symbExecVars, services);
        ruleApp.setInformationFlowProofObligationVars(ifVars);

        // set execution context
        ruleApp.setExecutionContext(inst.innermostExecutionContext);

        // create proof obligation
        InfFlowPOSnippetFactory f =
                POSnippetFactory.getInfFlowFactory(inv, ifVars.c1, ifVars.c2,
                                                   inst.innermostExecutionContext,
                                                   TB.var(guardVar),
                                                   services);
        final Term selfComposedExec =
                f.create(InfFlowPOSnippetFactory.Snippet.SELFCOMPOSED_LOOP_WITH_INV_RELATION);
        final Term post = f.create(InfFlowPOSnippetFactory.Snippet.INF_FLOW_INPUT_OUTPUT_RELATION);

        final Term finalTerm =
                TB.imp(TB.label(selfComposedExec,
                                SelfCompositionTermLabel.INSTANCE), post);
        infFlowGoal.proof().addLabeledIFSymbol(selfComposedExec);
        infFlowGoal.addFormula(new SequentFormula(finalTerm), false, true);

        return infFlowData;
    }

    //-------------------------------------------------------------------------
    //public interface
    //-------------------------------------------------------------------------

    @Override
    public boolean isApplicable(Goal goal, PosInOccurrence pio) {
        return checkApplicability(goal,pio);
    }

    //focus must be top level succedent
    static boolean checkApplicability (Goal g, PosInOccurrence pio) {
        if (pio == null || !pio.isTopLevel() || pio.isInAntec())
            return false;
        final Pair<Term, Term> up = applyUpdates(pio.subTerm());
        final Term progPost = up.second;
        if (!checkFocus(progPost)) {
            return false;
        }

        // active statement must be while loop
        final SourceElement activeStatement = JavaTools.getActiveStatement(progPost.javaBlock());
        if (!(activeStatement instanceof While)) {
            return false;
        }
        return true;
    }


    static Pair<Term, Term> applyUpdates(Term focusTerm) {
        if (focusTerm.op() instanceof UpdateApplication) {
            return new Pair<Term, Term>(UpdateApplication.getUpdate(focusTerm),
                    UpdateApplication.getTarget(focusTerm));
        } else {
            return new Pair<Term, Term>(TB.skip(), focusTerm);
        }
    }

    @Override
    public ImmutableList<Goal> apply(Goal goal, Services services, final RuleApp ruleApp)
            throws RuleAbortException {
        assert ruleApp instanceof LoopInvariantBuiltInRuleApp;
        LoopInvariantBuiltInRuleApp loopRuleApp =
                (LoopInvariantBuiltInRuleApp) ruleApp;

        final Sequent applicationSequent = goal.sequent();
        final KeYJavaType booleanKJT = services.getTypeConverter().getBooleanType();

        //get instantiation
        final Instantiation inst = instantiate(loopRuleApp, services);

        final Map<LocationVariable,Term> atPres = inst.inv.getInternalAtPres();
        final List<LocationVariable> heapContext = ((IBuiltInRuleApp)ruleApp).getHeapContext();        

        Term invTerm = null;
        for(LocationVariable heap : heapContext) {
            final Term i = inst.inv.getInvariant(heap, inst.selfTerm, atPres, services);
      if(i == null) continue;
            if(invTerm == null) {
                invTerm = i;
            } else{
                invTerm = TB.and(invTerm, i);
            }
        }

        final Map<LocationVariable,Term> mods = new LinkedHashMap<LocationVariable,Term>();
        for(LocationVariable heap : heapContext) {
            final Term m = inst.inv.getModifies(heap, inst.selfTerm, atPres, services);
            mods.put(heap, m);
        }

        final Term variant = inst.inv.getVariant(inst.selfTerm, atPres, services);

        //collect input and output local variables, 
        //prepare reachableIn and reachableOut
        final ImmutableSet<ProgramVariable> localIns =
                MiscTools.getLocalIns(inst.loop, services);
        final ImmutableSet<ProgramVariable> localOuts =
                MiscTools.getLocalOuts(inst.loop, services);
        Term reachableIn = TB.tt();
        for(ProgramVariable pv : localIns) {
            reachableIn = TB.and(reachableIn, 
                    TB.reachableValue(services, pv));
        }
        Term reachableOut = TB.tt();
        for(ProgramVariable pv : localOuts) {
            reachableOut = TB.and(reachableOut, 
                    TB.reachableValue(services, pv));
        }

        //prepare variant
	final ProgramElementName variantName 
		= new ProgramElementName(TB.newName(services, "variant"));
	final LocationVariable variantPV = new LocationVariable(variantName, Sort.ANY);
								//intKJT);
	services.getNamespaces().programVariables().addSafely(variantPV);
	
	final boolean dia = ((Modality)inst.progPost.op()).terminationSensitive();
	final Term variantUpdate 
		= dia ? TB.elementary(services, variantPV, variant) : TB.skip();
	final Term variantNonNeg 
		= TB.tt(); // ? TB.leq(TB.zero(services), variant, services) : TB.tt();
	final Term variantPO
		= dia ? TB.prec(variant, TB.var(variantPV), services)
//		        TB.and(variantNonNeg, 
//			       TB.lt(variant, TB.var(variantPV), services)) 
                      : TB.tt();
        
        //prepare guard
        final ProgramElementName guardVarName = new ProgramElementName(TB.newName(services, "b"));
        final LocationVariable guardVar = new LocationVariable(guardVarName, booleanKJT);
        services.getNamespaces().programVariables().addSafely(guardVar);
        loopRuleApp.setGuard(TB.var(guardVar));
        final VariableSpecification guardVarSpec =
                new VariableSpecification(guardVar, inst.loop.getGuardExpression(), booleanKJT);
        final LocalVariableDeclaration guardVarDecl =
                new LocalVariableDeclaration(new TypeRef(booleanKJT), guardVarSpec);
        final Statement guardVarMethodFrame =
                inst.innermostExecutionContext == null ?
                        guardVarDecl : new MethodFrame(null, inst.innermostExecutionContext,
                                                       new StatementBlock(guardVarDecl));
        final JavaBlock guardJb =
                JavaBlock.createJavaBlock(new StatementBlock( guardVarMethodFrame));
        final Term guardTrueTerm = TB.equals(TB.var(guardVar), TB.TRUE(services));
        final Term guardFalseTerm = TB.equals(TB.var(guardVar), TB.FALSE(services));

        Term beforeLoopUpdate = null;

        final Map<LocationVariable,Map<Term,Term>> heapToBeforeLoop =
                new LinkedHashMap<LocationVariable,Map<Term,Term>>();

        for(LocationVariable heap : heapContext) {
            heapToBeforeLoop.put(heap, new LinkedHashMap<Term,Term>());
            final LocationVariable lv =
                    TB.heapAtPreVar(services, heap+"Before_LOOP", heap.sort(), true);
            services.getNamespaces().programVariables().addSafely(lv);
            final Term u = TB.elementary(services, lv, TB.var(heap));
            if (beforeLoopUpdate == null) {
                beforeLoopUpdate = u;
            } else {
                beforeLoopUpdate = TB.parallel(beforeLoopUpdate, u);
            }
            heapToBeforeLoop.get(heap).put(TB.var(heap), TB.var(lv));
        }

        for (ProgramVariable pv : localOuts) {
            final String pvBeforeLoopName
            = TB.newName(services, pv.name().toString() + "Before_" + inst.inv.getName());
            final LocationVariable pvBeforeLoop
            = new LocationVariable(new ProgramElementName(pvBeforeLoopName), pv.getKeYJavaType());
            services.getNamespaces().programVariables().addSafely(pvBeforeLoop);
            beforeLoopUpdate = TB.parallel(beforeLoopUpdate,
                                           TB.elementary(services,
                                                         pvBeforeLoop, 
                                                         TB.var(pv)));
            heapToBeforeLoop.get(services.getTypeConverter().getHeapLDT().getHeap())
                    .put(TB.var(pv), TB.var(pvBeforeLoop));
        }

        //prepare anon update, frame condition, etc.
        Term anonUpdate = createLocalAnonUpdate(localOuts, services); // can still be null
        //Term anonAssumption = null;
        Term wellFormedAnon = null;
        Term frameCondition = null;
        Term reachableState = null;
        ImmutableList<AnonUpdateData> anonUpdateDatas =
                ImmutableSLList.<AnonUpdateData>nil();
        for (LocationVariable heap : heapContext) {
            final AnonUpdateData tAnon
            = createAnonUpdate(heap, mods.get(heap), inst.inv, services);
            anonUpdateDatas = anonUpdateDatas.append(tAnon);
            if(anonUpdate == null) {
                anonUpdate = tAnon.anonUpdate;
            } else{
                anonUpdate = TB.parallel(anonUpdate, tAnon.anonUpdate);
            }
            if(wellFormedAnon == null) {
                wellFormedAnon = TB.wellFormed(tAnon.anonHeap, services);
            } else{
                wellFormedAnon = TB.and(wellFormedAnon, TB.wellFormed(tAnon.anonHeap, services));
            }
            final Term m = mods.get(heap);
            final Term fc;
          if (TB.strictlyNothing().equals(m) &&
                  heap == services.getTypeConverter().getHeapLDT().getHeap()) {
                fc = TB.frameStrictlyEmpty(services, TB.var(heap), heapToBeforeLoop.get(heap)); 
            } else{
                fc = TB.frame(services, TB.var(heap), heapToBeforeLoop.get(heap), m);
            }
            if(frameCondition == null){
                frameCondition = fc;
            } else{
                frameCondition = TB.and(frameCondition, fc);
            }
            if (reachableState == null) {
                reachableState = TB.wellFormed(heap, services);
              } else {
                reachableState = TB.and(reachableState, TB.wellFormed(heap, services));
              }
        }

        //prepare common assumption
        final Term[] uAnon 
        = new Term[]{inst.u, anonUpdate};
        final Term[] uBeforeLoopDefAnonVariant =
                new Term[]{inst.u,
                           beforeLoopUpdate,
                           anonUpdate,
                           variantUpdate};
        final Term uAnonInv = TB.applySequential(uAnon, TB.and(invTerm, reachableOut));
        final Term uAnonInvVariantNonNeg = TB.applySequential(uAnon,
                                                              TB.and(new Term[]{invTerm,
                                                                                reachableOut,
                                                                                variantNonNeg}));
	final WhileInvariantTransformer wir = new WhileInvariantTransformer();
        SVInstantiations svInst
        = SVInstantiations.EMPTY_SVINSTANTIATIONS.replace(null, null,
                                                          inst.innermostExecutionContext,
                                                          null, services);
        for(SchemaVariable sv : wir.neededInstantiations(inst.loop, svInst)) {
            assert sv instanceof ProgramSV;
            svInst = svInst.addInteresting(sv,
                                           (Name) new ProgramElementName(sv.name().toString()),
                                           services);
        }

        final Term invTerm2;
        final StrategyProperties props =
                goal.proof().getSettings().getStrategySettings().getActiveStrategyProperties();
        final boolean queryTreatmenIsOn =
                props.getProperty(StrategyProperties.QUERY_OPTIONS_KEY)
                    == StrategyProperties.QUERY_ON;
        if(queryTreatmenIsOn ||
           props.getProperty(StrategyProperties.QUERY_OPTIONS_KEY)
               == StrategyProperties.QUERY_RESTRICTED){
            invTerm2 = QueryExpand.INSTANCE
                    .evaluateQueries(services, invTerm, true, queryTreatmenIsOn); //chrisg
        } else {
            invTerm2 = invTerm;
        }

        //split goal into three branches
        final ImmutableList<Goal> result = goal.split(3);
        final Goal initGoal = result.tail().tail().head();
        final Goal bodyGoal = result.tail().head();
        final Goal useGoal = result.head();

        initGoal.setBranchLabel("Invariant Initially Valid");
        bodyGoal.setBranchLabel("Body Preserves Invariant");
        useGoal.setBranchLabel("Use Case");

        
        // set up bodyGoal
        Term bodyTerm = wir.transform(this,
                                      bodyGoal,
                                      applicationSequent,
                                      ruleApp.posInOccurrence(),
                                      inst.progPost,
                                      TB.and(new Term[]{invTerm2, frameCondition, variantPO}),
                                      svInst,
                                      services);
        final Term guardTrueBody = TB.imp(TB.box(guardJb,guardTrueTerm), bodyTerm);

        //"Body Preserves Invariant":
        // \replacewith (==>  #atPreEqs(anon1)
        //                       -> #introNewAnonUpdate(
        //                                  #modifies,
        //                                  #locDepFunc(anon1, \[{.. while (#e) #s ...}\]post)
        //                          & inv ->
        //                         (\[{ method-frame(#ex):{#typeof(#e) #v1 = #e;} }\]#v1=TRUE ->
        //                          #whileInvRule(\[{.. while (#e) #s ...}\]post,
        //                               #locDepFunc(anon1, \[{.. while (#e) #s ...}\]post)
        //                                  & inv)),
        //                          anon1));
        bodyGoal.addFormula(new SequentFormula(wellFormedAnon),
                true,
                false);

        bodyGoal.addFormula(new SequentFormula(uAnonInvVariantNonNeg),
                true,
                false);

        bodyGoal.changeFormula(new SequentFormula(TB.applySequential(
                uBeforeLoopDefAnonVariant,
                guardTrueBody)),
                ruleApp.posInOccurrence());

        if (isInfFlowProof(inst, goal, services)) {
            // reset validiy branch

            bodyGoal.setBranchLabel("Information Flow Validity");

            // clear goal
            bodyGoal.node().setSequent(Sequent.EMPTY_SEQUENT);
            bodyGoal.clearAndDetachRuleAppIndex();

            // set up information flow validity goal
            InfFlowData infFlowData =
                    setUpInfFlowValidityGoal(bodyGoal, loopRuleApp, inst, guardVar,
                                             guardJb, localIns, localOuts,
                                             anonUpdateDatas, anonUpdate,
                                             services);

            // set up information flow part of useGoal:
            // add infFlowAssumptions, add term and taclet to post goal
            setUpInfFlowPartOfUseGoal(infFlowData,
                                      anonUpdateDatas.head().loopHeapAtPre,
                                      useGoal);
        }

        //"Invariant Initially Valid":
        // \replacewith (==> inv );
        initGoal.changeFormula(new SequentFormula(TB.apply(inst.u,
                                                           TB.and(variantNonNeg,
                                                                  TB.and(invTerm, reachableState)),
                                                           null)),
                               ruleApp.posInOccurrence());
        if (TermLabelWorkerManagement.hasInstantiators(services)) {
           TermLabelWorkerManagement.updateLabels(null, ruleApp.posInOccurrence(), this, initGoal);
        }

        // "Use Case":
        // \replacewith (==> #introNewAnonUpdate(#modifies, inv ->
        // (\[{ method-frame(#ex):{#typeof(#e) #v1 = #e;} }\]
        // (#v1=FALSE -> \[{.. ...}\]post)),anon2))

        useGoal.addFormula(new SequentFormula(wellFormedAnon), true, false);
        useGoal.addFormula(new SequentFormula(uAnonInv), true, false);

	JavaBlock useJavaBlock = JavaTools.removeActiveStatement(inst.progPost.javaBlock(), services);
	Term restPsi =
	        TB.prog((Modality)inst.progPost.op(), useJavaBlock, inst.progPost.sub(0),
	                TermLabelWorkerManagement.instantiateLabels(
	                        services, ruleApp.posInOccurrence(), this, useGoal, null,
	                        inst.progPost.op(), new ImmutableArray<Term>(inst.progPost.sub(0)),
	                        null, useJavaBlock));
        final Term guardFalseRestPsi = TB.imp(TB.box(guardJb,guardFalseTerm), restPsi);
        useGoal.changeFormula(new SequentFormula(TB.applySequential(uAnon, guardFalseRestPsi)),
                              ruleApp.posInOccurrence());

        return result;
    }


    private boolean isInfFlowProof(Instantiation inst,
                                   Goal goal,
                                   Services services) {
        LoopInvariant inv = inst.inv;
        final boolean isInfFlow = isInfFlow(goal);
        final boolean hasIFSpecs = inv.hasInfFlowSpec(services);
        return isInfFlow && hasIFSpecs;
    }


    @Override
    public Name name() {
	return NAME;
    }


    @Override
    public String displayName() {
	return toString();
    }


    @Override
    public String toString() {
	return NAME.toString();
    }


    @Override
    public LoopInvariantBuiltInRuleApp createApp(PosInOccurrence pos) {
        return new LoopInvariantBuiltInRuleApp(this, pos);
    }

    //-------------------------------------------------------------------------
    //inner classes
    //-------------------------------------------------------------------------

    private static final class Instantiation {
	public final Term u;
	public final Term progPost;
	public final While loop;
	public final LoopInvariant inv;
	public final Term selfTerm;
	public final ExecutionContext innermostExecutionContext;

	public Instantiation(Term u, 
			     Term progPost, 
			     While loop,
			     LoopInvariant inv,
			     Term selfTerm,
			     ExecutionContext innermostExecutionContext) {
	    assert u != null;
	    assert u.sort() == Sort.UPDATE;
	    assert progPost != null;
	    assert progPost.sort() == Sort.FORMULA;
	    assert loop != null;
	    assert inv != null;
	    this.u = u;
	    this.progPost = progPost;
	    this.loop = loop;
	    this.inv = inv;
	    this.selfTerm = selfTerm;
	    this.innermostExecutionContext = innermostExecutionContext;
	}
    }

    private static class AnonUpdateData {

        public final Term anonUpdate, anonHeap, loopHeap, loopHeapAtPre;


        public AnonUpdateData(Term anonUpdate,
                              Term loopHeap,
                              Term loopHeapAtPre,
                              Term anonHeap) {
            this.anonUpdate = anonUpdate;
            this.loopHeap = loopHeap;
            this.loopHeapAtPre = loopHeapAtPre;
            this.anonHeap = anonHeap;
        }
    }

    private static final class InfFlowData {
        public final ProofObligationVars symbExecVars;
        public final Term guardAtPre;
        public final Term guardAtPost;
        public final JavaBlock guardJb;
        public final Term guardTerm;
        public final ImmutableList<Term> localOuts;
        public final ImmutableList<Term> localOutsAtPre;
        public final ImmutableList<Term> localOutsAtPost;
        public final Pair<Term, Term> updates;
        public final Term applPredTerm;
        public final Taclet infFlowApp;

        private InfFlowData(ProofObligationVars symbExecVars,
                            Term guardAtPre,
                            Term guardAtPost,
                            JavaBlock guardJb,
                            Term guardTerm,
                            ImmutableList<Term> localOuts,
                            ImmutableList<Term> localOutsAtPre,
                            ImmutableList<Term> localOutsAtPost,
                            Pair<Term, Term> updates,
                            Term applPredTerm,
                            Taclet infFlowApp) {
            this.symbExecVars = symbExecVars;
            this.guardAtPre = guardAtPre;
            this.guardAtPost = guardAtPost;
            this.guardJb = guardJb;
            this.guardTerm = guardTerm;
            this.localOuts = localOuts;
            this.localOutsAtPre = localOutsAtPre;
            this.localOutsAtPost = localOutsAtPost;
            this.updates = updates;
            this.infFlowApp = infFlowApp;
            this.applPredTerm = applPredTerm;

            assert symbExecVars != null;
            assert guardAtPre != null;
            assert guardAtPost != null;
            assert guardJb != null;
            assert guardTerm != null;
            assert localOuts != null;
            assert localOutsAtPre != null;
            assert localOutsAtPost != null;
            assert updates != null;
            assert applPredTerm != null;
            assert infFlowApp != null;
        }
    }
}