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

import java.util.ArrayList;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.List;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.JavaTools;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.Statement;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.PrimitiveType;
import de.uka.ilkd.key.java.declaration.LocalVariableDeclaration;
import de.uka.ilkd.key.java.declaration.VariableSpecification;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.reference.TypeRef;
import de.uka.ilkd.key.java.statement.MethodFrame;
import de.uka.ilkd.key.java.statement.While;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.InfFlowCheckInfo;
import de.uka.ilkd.key.proof.init.InfFlowContractPO;
import de.uka.ilkd.key.proof.init.ProofObligationVars;
import de.uka.ilkd.key.proof.init.InfFlowContractPO.IFProofObligationVars;
import de.uka.ilkd.key.proof.init.po.snippet.InfFlowPOSnippetFactory;
import de.uka.ilkd.key.proof.init.po.snippet.POSnippetFactory;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.rule.metaconstruct.WhileInvRule;
import de.uka.ilkd.key.rule.tacletbuilder.RemovePostTacletBuilder;
import de.uka.ilkd.key.rule.tacletbuilder.SplitPostTacletBuilder;
import de.uka.ilkd.key.speclang.LoopInvariant;
import de.uka.ilkd.key.strategy.StrategyProperties;
import de.uka.ilkd.key.util.MiscTools;
import de.uka.ilkd.key.util.Pair;

public final class WhileInvariantRule implements BuiltInRule {


    public static final WhileInvariantRule INSTANCE = new WhileInvariantRule();

    private static final Name NAME = new Name("Use Loop Invariant");
    private static final TermBuilder TB = TermBuilder.DF;

    private Term lastFocusTerm;
    private Instantiation lastInstantiation;


    //-------------------------------------------------------------------------
    //constructors
    //-------------------------------------------------------------------------

    private WhileInvariantRule() {
    }


    //-------------------------------------------------------------------------
    //internal methods
    //-------------------------------------------------------------------------

    private Instantiation instantiate(final LoopInvariantBuiltInRuleApp app, Services services)
            throws RuleAbortException {
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


    private Term createLocalAnonUpdate(ImmutableSet<ProgramVariable> localOuts, Services services) {
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
        final boolean loadedInfFlow = services.getProof().getSettings()
                                        .getStrategySettings().getActiveStrategyProperties()
                                        .getProperty(StrategyProperties.INF_FLOW_CHECK_PROPERTY)
                                        .equals(StrategyProperties.INF_FLOW_CHECK_TRUE);
	final HeapLDT heapLDT = services.getTypeConverter().getHeapLDT();
	final Name loopHeapName = new Name(TB.newName(services, heap+"_After_LOOP"));
	final Function loopHeapFunc = new Function(loopHeapName, heapLDT.targetSort(), true);
	if (!loadedInfFlow)
	    services.getNamespaces().functions().addSafely(loopHeapFunc);

        final Term loopHeap = TB.func(loopHeapFunc);
	final Name anonHeapName = new Name(TB.newName(services, "anon_"+heap+"_LOOP"));
	final Function anonHeapFunc = new Function(anonHeapName,heap.sort(), true);
	if (!loadedInfFlow)
	    services.getNamespaces().functions().addSafely(anonHeapFunc);
	final Term anonHeap = TB.func(anonHeapFunc);

	// check for strictly pure loops
	final Term anonUpdate;
	if(TB.strictlyNothing().equals(mod)) {
	    anonUpdate = TB.skip();
	} else {
	    anonUpdate = TB.anonUpd(heap, services, mod, anonHeap);
	}

	return new AnonUpdateData(anonUpdate, loopHeap, TB.getBaseHeap(services), anonHeap);
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

    private static ImmutableList<Term> buildLocalIns(ImmutableList<Term> varTerms,
                                                     Services services) {
        if (varTerms == null || varTerms.isEmpty()) {
            return varTerms;
        }
        ImmutableList<Term> localIns = ImmutableSLList.<Term>nil();
        for(final Term varTerm: varTerms) {
            assert varTerm.op() instanceof LocationVariable;        

            final KeYJavaType resultType = ((LocationVariable)varTerm.op()).getKeYJavaType();

            final String name = TermBuilder.DF.newName(services, varTerm.toString() + "_Before");
            final LocationVariable varAtPreVar =
                    new LocationVariable(new ProgramElementName(name), resultType);
            register(varAtPreVar, services);
            final Term varAtPre = TermBuilder.DF.var(varAtPreVar);
            localIns = localIns.append(varAtPre);
        }
        return localIns;
    }

    private static ImmutableList<Term> buildLocalOuts(ImmutableList<Term> varTerms,
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

    public static FindTaclet loadFindTaclet(LoopInvariant loopInv, Services services) {
        Taclet res = null;
        if (!InfFlowContractPO.hasSymbols()) {
            InfFlowContractPO.newSymbols(
                    services.getProof().env().getInitConfig().activatedTaclets());
        }
        for (int j = 0; j < 10000; j++) {
            String name =
                    MiscTools.toValidTacletName("unfold computed formula " + j + " of " +
                            loopInv.getUniqueName()).toString();
            res = InfFlowContractPO.getTaclet(name);
            if (res != null)
                return (FindTaclet)res;
        }
        assert false; // This should not happen
        return null;
    }

    public static Term loadFindTerm(LoopInvariant loopInv, Services services) {
        return loadFindTaclet(loopInv, services).find();
    }

    private Goal buildInfFlowValidityGoal(Goal goal, LoopInvariant inv,
                                          InfFlowData infFlowData,
                                          RuleApp ruleApp,                                          
                                          Goal infFlowGoal) {
        // generate proof obligation variables
        final ProofObligationVars instantiationVars =
                new ProofObligationVars(infFlowData.selfTerm,
                                        infFlowData.selfAtPost,
                                        infFlowData.guardAtPre,
                                        infFlowData.newIns,
                                        infFlowData.heapAtPre,
                                        infFlowData.guardAtPost,
                                        infFlowData.newOuts,
                                        infFlowData.heapAtPost,
                                        infFlowData.services,
                                        true);

        final IFProofObligationVars ifVars =
                new IFProofObligationVars(instantiationVars, infFlowData.services, true);
        ((LoopInvariantBuiltInRuleApp) ruleApp).setInformationFlowProofObligationVars(ifVars);

        // create proof obligation
        InfFlowPOSnippetFactory f =
                POSnippetFactory.getInfFlowFactory(inv, ifVars.c1, ifVars.c2, infFlowData.services);
        final Term selfComposedExec =
                f.create(InfFlowPOSnippetFactory.Snippet.SELFCOMPOSED_LOOP_WITH_INV_RELATION);
        final Term post = f.create(InfFlowPOSnippetFactory.Snippet.INF_FLOW_INPUT_OUTPUT_RELATION);

        final Term finalTerm = TB.imp(selfComposedExec, post);

        final Sequent seq =
                Sequent.createSuccSequent(new Semisequent(new SequentFormula(finalTerm)));
        infFlowGoal = goal.getCleanGoal(seq);
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

        return infFlowGoal;
    }

    private Goal addInfFlowAssumptionsAndTaclet(InfFlowData infData, Goal goal) {
        final Term heapAtPreEq =
                TB.equals(infData.heapAtPre, infData.baseHeap);
        final Term heapAtPostEq =
                TB.equals(infData.heapAtPost, infData.baseHeap);
        Term beforeAssumptions = TB.and(heapAtPreEq,
                                        TB.box(infData.guardJb,
                                               TB.equals(infData.guardAtPre,
                                                         infData.guardTerm)));
        final Iterator<Term> newIns = infData.newIns.iterator();
        for (final Term locIn: infData.localIns) {
            beforeAssumptions = TB.and(beforeAssumptions, TB.equals(newIns.next(), locIn));
        }

        Term afterAssumptions = TB.and(heapAtPostEq,
                                       TB.box(infData.guardJb,
                                              TB.equals(infData.guardAtPost,
                                                        infData.guardTerm)),
                                       TB.equals(infData.selfAtPost, infData.selfTerm));
        final Iterator<Term> newOuts = infData.newOuts.iterator();
        for (final Term locOut: infData.localOuts) {
            afterAssumptions = TB.and(afterAssumptions, TB.equals(newOuts.next(), locOut));
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

        return goal;
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
        final boolean loadedInfFlow = services.getProof().getSettings()
                                        .getStrategySettings().getActiveStrategyProperties()
                                        .getProperty(StrategyProperties.INF_FLOW_CHECK_PROPERTY)
                                        .equals(StrategyProperties.INF_FLOW_CHECK_TRUE);
        final KeYJavaType booleanKJT = services.getTypeConverter().getBooleanType();
        final KeYJavaType intKJT =
                services.getJavaInfo().getPrimitiveKeYJavaType(PrimitiveType.JAVA_INT);

        //get instantiation
        final Instantiation inst = instantiate((LoopInvariantBuiltInRuleApp) ruleApp, services);

        final Map<LocationVariable,Term> atPres = inst.inv.getInternalAtPres();
        final List<LocationVariable> heapContext = ((IBuiltInRuleApp)ruleApp).getHeapContext();        

        Term invTerm = null;
        for(LocationVariable heap : heapContext) {
            final Term i = inst.inv.getInvariant(heap, inst.selfTerm, atPres, services);
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
        final ProgramElementName variantName =
                new ProgramElementName(TB.newName(services, "variant"));
        final LocationVariable variantPV = new LocationVariable(variantName, intKJT);
        services.getNamespaces().programVariables().addSafely(variantPV);

        final boolean dia = ((Modality)inst.progPost.op()).terminationSensitive();
        final Term variantUpdate =
                dia ? TB.elementary(services, variantPV, variant) : TB.skip();
        final Term variantNonNeg =
                dia ? TB.leq(TB.zero(services), variant, services) : TB.tt();
        final Term variantPO = dia ?
                TB.and(variantNonNeg, TB.lt(variant, TB.var(variantPV), services))
                : TB.tt();
        //prepare guard
        final ProgramElementName guardVarName = new ProgramElementName(TB.newName(services, "b"));
        final LocationVariable guardVar = new LocationVariable(guardVarName, booleanKJT);
        if (!loadedInfFlow)
            services.getNamespaces().programVariables().addSafely(guardVar);
        final VariableSpecification guardVarSpec 
        = new VariableSpecification(guardVar, 
                inst.loop.getGuardExpression(), 
                booleanKJT);        
        final LocalVariableDeclaration guardVarDecl 
        = new LocalVariableDeclaration(new TypeRef(booleanKJT), 
                guardVarSpec);
        final Statement guardVarMethodFrame 
        = inst.innermostExecutionContext == null 
        ? guardVarDecl
                : new MethodFrame(null, 
                        inst.innermostExecutionContext,
                        new StatementBlock(guardVarDecl));
        final JavaBlock guardJb
        = JavaBlock.createJavaBlock(new StatementBlock(
                guardVarMethodFrame));
        final Term guardTrueTerm = TB.equals(TB.var(guardVar),
                TB.TRUE(services));
        final Term guardFalseTerm = TB.equals(TB.var(guardVar),
                TB.FALSE(services));

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

        final WhileInvRule wir = (WhileInvRule) AbstractTermTransformer.WHILE_INV_RULE;
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

        Term bodyTerm = TB.tf().createTerm(wir,
                                           inst.progPost,
                                           TB.and(new Term[]{invTerm2, frameCondition, variantPO}));
        bodyTerm = wir.transform(bodyTerm, svInst, services);
	final Term guardTrueBody = TB.imp(TB.box(guardJb,guardTrueTerm), bodyTerm);

        Goal infFlowGoal = null;
        InfFlowData infFlowData = null;

        if (((goal.getStrategyInfo(InfFlowCheckInfo.INF_FLOW_CHECK_PROPERTY) != null &&
            goal.getStrategyInfo(InfFlowCheckInfo.INF_FLOW_CHECK_PROPERTY)) || loadedInfFlow) &&
            inst.inv.getRespects(services) != null) {

            assert anonUpdateDatas.size() == 1 : "information flow " +
                                                 "extension is at the " +
                                                 "moment not compatible " +
                                                 "with the non-base-heap " +
                                                 "setting";
            final AnonUpdateData anonUpdateData = anonUpdateDatas.head();
            final Term baseHeap = anonUpdateData.loopHeapAtPre;
                    //heapContext.get(0);
            final Term guardTerm = TB.var(guardVar);
            final Term selfTerm = inst.selfTerm;
            inst.inv.setGuard(guardTerm, services);
            services.getSpecificationRepository().addLoopInvariant(inst.inv);

            final Term heapAtPre = TB.var(TB.heapAtPreVar(services, baseHeap + "_Before_LOOP",
                                                          baseHeap.sort(), false));
            final Term heapAtPost = anonUpdateData.loopHeap;
            final Term guardAtPre = buildBeforeVar(guardTerm, services);
            final Term guardAtPost = buildAfterVar(guardTerm, services);            
            final Term selfAtPost = buildAtPostVar(selfTerm, "LOOP", services);
            final ImmutableList<Term> localInTerms = MiscTools.toTermList(localIns);
            final ImmutableList<Term> newLocalIns = buildLocalIns(localInTerms, services);
            final ImmutableList<Term> localOutTerms = MiscTools.toTermList(localOuts);
            final ImmutableList<Term> newLocalOuts = buildLocalOuts(localOutTerms, services);
            final Pair<Term, Term> updates = new Pair<Term, Term> (inst.u, anonUpdate);

            final InfFlowLoopInvariantTacletBuilder ifInvariantBuilder =
                    new InfFlowLoopInvariantTacletBuilder(services);            

            ifInvariantBuilder.setInvariant(inst.inv);
            ifInvariantBuilder.setGuard(guardAtPre);
            ifInvariantBuilder.setGuardAtPost(guardAtPost);
            ifInvariantBuilder.setContextUpdate(/*inst.u*/);
            ifInvariantBuilder.setHeapAtPre(heapAtPre);
            ifInvariantBuilder.setHeapAtPost(heapAtPost);
            ifInvariantBuilder.setSelf(selfTerm);
            ifInvariantBuilder.setSelfAtPost(selfAtPost);
            ifInvariantBuilder.setLocalIns(newLocalIns);
            ifInvariantBuilder.setLocalOuts(newLocalOuts);

            // generate information flow invariant application predicate
            // and associated taclet
            final Term loopInvApplPredTerm =
                    ifInvariantBuilder.buildContractApplPredTerm(true);
            if (!InfFlowContractPO.hasSymbols()) {
                InfFlowContractPO.newSymbols(
                        services.getProof().env().getInitConfig().activatedTaclets());
            }
            final Taclet informationFlowInvariantApp =
                    ifInvariantBuilder.buildContractApplTaclet(true);
            infFlowData = new InfFlowData(heapAtPre, heapAtPost, baseHeap, services,
                                          selfTerm, selfAtPost,
                                          guardAtPre, guardAtPost, guardJb, guardTerm,
                                          localInTerms, newLocalIns, localOutTerms, newLocalOuts,
                                          updates, loopInvApplPredTerm, informationFlowInvariantApp);

            // create information flow validity goal
            infFlowGoal = buildInfFlowValidityGoal(goal, inst.inv, infFlowData, ruleApp, infFlowGoal);
        } else {
            infFlowData = new InfFlowData();
        }

        //split goal into three branches
        final Goal initGoal;
        Goal useGoal;
        ImmutableList<Goal> result;
        if (!infFlowData.isInfFlow) {
            result = goal.split(3);
            initGoal = result.tail().tail().head();
            final Goal bodyGoal = result.tail().head();
            useGoal = result.head();
            initGoal.setBranchLabel("Invariant Initially Valid");
            bodyGoal.setBranchLabel("Body Preserves Invariant");
            useGoal.setBranchLabel("Use Case");

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
        } else {
            result = goal.split(2);
            initGoal = result.tail().head();
            useGoal = result.head();
            initGoal.setBranchLabel("Invariant Initially Valid");
            useGoal.setBranchLabel("Use Case");
            result = result.append(infFlowGoal);

            // set infFlowAssumptions, add term and taclet to post goal
            useGoal = addInfFlowAssumptionsAndTaclet(infFlowData, useGoal);
        }

        //"Invariant Initially Valid":
        // \replacewith (==> inv );
        initGoal.changeFormula(new SequentFormula(TB.apply(inst.u,
                                                           TB.and(variantNonNeg,
                                                                  TB.and(invTerm, reachableState)))),
                               ruleApp.posInOccurrence());

        // "Use Case":
        // \replacewith (==> #introNewAnonUpdate(#modifies, inv ->
        // (\[{ method-frame(#ex):{#typeof(#e) #v1 = #e;} }\]
        // (#v1=FALSE -> \[{.. ...}\]post)),anon2))

        useGoal.addFormula(new SequentFormula(wellFormedAnon), true, false);
        useGoal.addFormula(new SequentFormula(uAnonInv), true, false);


        final Term restPsi = TB.prog((Modality)inst.progPost.op(),
                                     JavaTools.removeActiveStatement(inst.progPost.javaBlock(),
                                                                     services),
                                     inst.progPost.sub(0));
        final Term guardFalseRestPsi = TB.imp(TB.box(guardJb,guardFalseTerm), restPsi);
        useGoal.changeFormula(new SequentFormula(TB.applySequential(uAnon, guardFalseRestPsi)),
                              ruleApp.posInOccurrence());

        return result;
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
        public final Term heapAtPre;
        public final Term heapAtPost;
        public final Term baseHeap;
        public final Services services;
        public final Term selfTerm;
        public final Term selfAtPost;
        public final Term guardAtPre;
        public final Term guardAtPost;
        public final JavaBlock guardJb;
        public final Term guardTerm;
        public final ImmutableList<Term> localIns;
        public final ImmutableList<Term> newIns;
        public final ImmutableList<Term> localOuts;
        public final ImmutableList<Term> newOuts;
        public final Pair<Term, Term> updates;
        public final Term applPredTerm;
        public final Taclet infFlowApp;
        public final boolean isInfFlow;

        public InfFlowData() {
            this.heapAtPre = null;
            this.heapAtPost = null;
            this.baseHeap = null;
            this.services = null;
            this.selfTerm = null;
            this.selfAtPost = null;
            this.guardAtPre = null;
            this.guardAtPost = null;
            this.guardJb = null;
            this.guardTerm = null;
            this.localIns = ImmutableSLList.<Term>nil();
            this.newIns = ImmutableSLList.<Term>nil();
            this.localOuts = ImmutableSLList.<Term>nil();
            this.newOuts = ImmutableSLList.<Term>nil();
            this.updates = new Pair<Term, Term> (null, null);
            this.infFlowApp = null;
            this.applPredTerm = null;
            this.isInfFlow = false;
        }

        public InfFlowData(Term heapAtPre, Term heapAtPost, Term baseHeap, Services services,
                           Term selfTerm, Term selfAtPost,
                           Term guardAtPre, Term guardAtPost, JavaBlock guardJb, Term guardTerm,
                           ImmutableList<Term> localIns, ImmutableList<Term> newIns,
                           ImmutableList<Term> localOuts, ImmutableList<Term> newOuts,
                           Pair<Term, Term> updates, Term applPredTerm, Taclet infFlowApp) {
            this.heapAtPre = heapAtPre;
            this.heapAtPost = heapAtPost;
            this.baseHeap = baseHeap;
            this.services = services;
            this.selfTerm = selfTerm;
            this.selfAtPost = selfAtPost;
            this.guardAtPre = guardAtPre;
            this.guardAtPost = guardAtPost;
            this.guardJb = guardJb;
            this.guardTerm = guardTerm;
            this.localIns = localIns;
            this.newIns = newIns;
            this.localOuts = localOuts;
            this.newOuts = newOuts;
            this.updates = updates;
            this.infFlowApp = infFlowApp;
            this.applPredTerm = applPredTerm;
            this.isInfFlow = true;
        }
    }
}