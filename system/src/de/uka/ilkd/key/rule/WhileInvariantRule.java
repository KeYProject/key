// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2011 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.rule;

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
import de.uka.ilkd.key.proof.init.ProofObligationVars;
import de.uka.ilkd.key.proof.init.po.snippet.BasicPOSnippetFactory;
import de.uka.ilkd.key.proof.init.po.snippet.InfFlowPOSnippetFactory;
import de.uka.ilkd.key.proof.init.po.snippet.POSnippetFactory;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.rule.metaconstruct.WhileInvRule;
import de.uka.ilkd.key.rule.tacletbuilder.RewriteTacletBuilder;
import de.uka.ilkd.key.rule.tacletbuilder.RewriteTacletGoalTemplate;
import de.uka.ilkd.key.speclang.LoopInvariant;
import de.uka.ilkd.key.strategy.StrategyProperties;
import de.uka.ilkd.key.util.MiscTools;
import de.uka.ilkd.key.util.Pair;

public final class WhileInvariantRule implements BuiltInRule {


    public static final WhileInvariantRule INSTANCE = new WhileInvariantRule();

    private static final Name NAME = new Name("Loop Invariant");
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
    
    private Instantiation instantiate(LoopInvariantBuiltInRuleApp app, Services services) throws RuleAbortException {
	
    Term focusTerm = app.posInOccurrence().subTerm();
        
    if(focusTerm == lastFocusTerm
	   && lastInstantiation.inv 
	       == services.getSpecificationRepository()
	                  .getLoopInvariant(lastInstantiation.loop)) {
	    return lastInstantiation;
	}

	//leading update?
	Pair<Term, Term> update = applyUpdates(focusTerm);
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
	final MethodFrame innermostMethodFrame 
		= JavaTools.getInnermostMethodFrame(progPost.javaBlock(), 
						    services);
	final Term selfTerm = innermostMethodFrame == null
	                      ? null
	                      : MiscTools.getSelfTerm(innermostMethodFrame, 
	                	      		      services);
	final ExecutionContext innermostExecutionContext 
		= innermostMethodFrame == null 
		  ? null
		  : (ExecutionContext) 
		          innermostMethodFrame.getExecutionContext();

	//cache and return result
	Instantiation result = new Instantiation(u, 
					         progPost, 
					         loop, 
					         inv,
					         selfTerm, 
					         innermostExecutionContext);
	lastFocusTerm = focusTerm;
	lastInstantiation = result;
	return result;
    }



    private Term createLocalAnonUpdate(ImmutableSet<ProgramVariable> localOuts, Services services) {
      Term anonUpdate = null;
      for(ProgramVariable pv : localOuts) {
        final String anonFuncName 
    	    = TB.newName(services, pv.name().toString());
        final Function anonFunc 
    	    = new Function(new Name(anonFuncName), pv.sort(), true);
        services.getNamespaces().functions().addSafely(anonFunc);
        final Term elemUpd = TB.elementary(services, (LocationVariable)pv, TB.func(anonFunc));
        if(anonUpdate == null) {
          anonUpdate = elemUpd;
        }else{
          anonUpdate = TB.parallel(anonUpdate, elemUpd);
        }
      }
      return anonUpdate;
    }
    
    /**
     * @return (anon update, anon heap)
     */    
    private static AnonUpdateData createAnonUpdate(LocationVariable heap,
	    			While loop, 
	    			Term mod,
	    			Services services) {
	final HeapLDT heapLDT = services.getTypeConverter().getHeapLDT();
	final Name loopHeapName 
        = new Name(TB.newName(services, heap.name()+"heapAfter_loop"));
        final Function loopHeapFunc = new Function(loopHeapName,
                                             heapLDT.targetSort(), true);
        services.getNamespaces().functions().addSafely(loopHeapFunc);
        final Term loopHeapTerm = TB.func(loopHeapFunc);
	final Name anonHeapName = new Name(TB.newName(services, "anon_"+heap.name()+"_loop"));
	final Function anonHeapFunc = new Function(anonHeapName,
					     heapLDT.targetSort(), true);
	services.getNamespaces().functions().addSafely(anonHeapFunc);
	final Term anonHeapTerm = TB.func(anonHeapFunc);
	
	final Term assumption = TB.equals(TB.anon(services, TB.var(heap), mod, anonHeapTerm),
	                                  loopHeapTerm);
	// check for strictly pure loops
	final Term anonUpdate;
	if(TB.lessThanNothing().equals(mod)) {
	    anonUpdate = TB.skip();
	} else {
	    anonUpdate = TB.anonUpd(heap, services, mod, anonHeapTerm);
	}
	
	return new AnonUpdateData(assumption, anonUpdate, anonHeapTerm, loopHeapTerm);
    }
    
    private Term createTermSV(String svName,
            Sort predArgSort,
            Services services) {
        Name name = services.getVariableNamer().getTemporaryNameProposal(svName);
        return TB.var(SchemaVariableFactory.createTermSV(name, predArgSort));
    }
    
    private static boolean checkFocus(final Term progPost) {
        // focus (below update) must be modality term
        return progPost.op() instanceof Modality;
    }
    
    //-------------------------------------------------------------------------
    //public interface
    //-------------------------------------------------------------------------

    @Override
    public boolean isApplicable(Goal goal, 
            PosInOccurrence pio) {
        return checkApplicability(goal,pio);
    }

    //focus must be top level succedent
    static boolean checkApplicability (Goal g, PosInOccurrence pio){
        if (pio == null || !pio.isTopLevel() || pio.isInAntec())
            return false;

        Pair<Term, Term> up = applyUpdates(pio.subTerm());
        final Term progPost = up.second;

        if (!checkFocus(progPost)) {
            return false;
        }

        // active statement must be while loop
        SourceElement activeStatement = JavaTools
        .getActiveStatement(progPost.javaBlock());
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
    public ImmutableList<Goal> apply(Goal goal, Services services, RuleApp ruleApp) throws RuleAbortException {
        final KeYJavaType booleanKJT = services.getTypeConverter()
        .getBooleanType();
        final KeYJavaType intKJT 
        = services.getJavaInfo()
        .getPrimitiveKeYJavaType(PrimitiveType.JAVA_INT);
        //get instantiation
        Instantiation inst = instantiate((LoopInvariantBuiltInRuleApp) ruleApp, services);	

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

        final Term variant = inst.inv.getVariant(inst.selfTerm, 
                atPres, 
                services);
        //collect input and output local variables, 
        //prepare reachableIn and reachableOut
        final ImmutableSet<ProgramVariable> localIns 
        = MiscTools.getLocalIns(inst.loop, services);
        final ImmutableSet<ProgramVariable> localOuts 
        = MiscTools.getLocalOuts(inst.loop, services);
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

        Term beforeLoopUpdate = null;

        final Map<LocationVariable,Map<Term,Term>> heapToBeforeLoop = new LinkedHashMap<LocationVariable,Map<Term,Term>>();

        for(LocationVariable heap : heapContext) {
            heapToBeforeLoop.put(heap, new LinkedHashMap<Term,Term>());
            final LocationVariable lv = TB.heapAtPreVar(services, heap.name()+"BeforeLoop", heap.sort(), true);
            services.getNamespaces().programVariables().addSafely(lv);
            final Term u = TB.elementary(services, lv, TB.var(heap));
            if(beforeLoopUpdate == null) {
                beforeLoopUpdate = u;
            }else{
                beforeLoopUpdate = TB.parallel(beforeLoopUpdate, u);
            }
            heapToBeforeLoop.get(heap).put(TB.var(heap), TB.var(lv));
        }

        for(ProgramVariable pv : localOuts) {
            final String pvBeforeLoopName 
            = TB.newName(services, pv.name().toString() + "BeforeLoop");
            final LocationVariable pvBeforeLoop 
            = new LocationVariable(new ProgramElementName(pvBeforeLoopName), 
                    pv.getKeYJavaType());
            services.getNamespaces().programVariables().addSafely(pvBeforeLoop);
            beforeLoopUpdate = TB.parallel(beforeLoopUpdate, 
                    TB.elementary(services, 
                            pvBeforeLoop, 
                            TB.var(pv)));
            heapToBeforeLoop.get(services.getTypeConverter().getHeapLDT().getHeap()).put(TB.var(pv), TB.var(pvBeforeLoop));
        }

        //prepare anon update, frame condition, etc.

        Term anonUpdate = createLocalAnonUpdate(localOuts, services); // can still be null
        Term assumption = TB.tt();
        Term loopHeap = TB.tt();
        Term wellFormedAnon = null;
        Term frameCondition = null;
        Term reachableState = reachableIn;
        for(LocationVariable heap : heapContext) {
            final AnonUpdateData tAnon
            = createAnonUpdate(heap, inst.loop, mods.get(heap), services);
            assumption = TB.and(assumption,tAnon.assumption);
            loopHeap = TB.and(loopHeap,tAnon.loopHeap);
            if(anonUpdate == null) {
                anonUpdate = tAnon.anonUpdate;
            }else{
                anonUpdate = TB.parallel(anonUpdate, tAnon.anonUpdate);
            }
            if(wellFormedAnon == null) {
                wellFormedAnon = TB.wellFormed(tAnon.anonHeap, services);
            }else{
                wellFormedAnon = TB.and(wellFormedAnon, TB.wellFormed(tAnon.anonHeap, services));
            }
            final Term m = mods.get(heap);
            final Term fc;
            if(TB.lessThanNothing().equals(m) && heap == services.getTypeConverter().getHeapLDT().getHeap()) {
                fc = TB.frameStrictlyEmpty(services, TB.var(heap), heapToBeforeLoop.get(heap)); 
            }else{
                fc = TB.frame(services, TB.var(heap), heapToBeforeLoop.get(heap), m);
            }
            if(frameCondition == null){
                frameCondition = fc;
            }else{
                frameCondition = TB.and(frameCondition, fc);
            }
            reachableState = TB.and(reachableState, TB.wellFormed(heap, services));
        }
        //prepare variant
        final ProgramElementName variantName 
        = new ProgramElementName(TB.newName(services, "variant"));
        final LocationVariable variantPV = new LocationVariable(variantName, 
                intKJT);
        services.getNamespaces().programVariables().addSafely(variantPV);

        final boolean dia = ((Modality)inst.progPost.op()).terminationSensitive();
        final Term variantUpdate 
        = dia ? TB.elementary(services, variantPV, variant) : TB.skip();
        final Term variantNonNeg 
        = dia ? TB.leq(TB.zero(services), variant, services) : TB.tt();
        final Term variantPO
        = dia ? TB.and(variantNonNeg, 
                TB.lt(variant, TB.var(variantPV), services)) 
                : TB.tt();

        //split goal into three branches
        ImmutableList<Goal> result = goal.split(3);
        Goal initGoal = result.tail().tail().head();
        Goal bodyGoal = result.tail().head();
        Goal useGoal = result.head();
        initGoal.setBranchLabel("Invariant Initially Valid");
        bodyGoal.setBranchLabel("Body Preserves Invariant");
        useGoal.setBranchLabel("Use Case");

        //prepare guard
        final ProgramElementName guardVarName 
        = new ProgramElementName(TB.newName(services, "b"));
        final LocationVariable guardVar = new LocationVariable(guardVarName, 
                booleanKJT);
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

        //prepare common assumption
        final Term[] uAnon 
        = new Term[]{inst.u, anonUpdate};
        final Term[] uBeforeLoopDefAnonVariant 
        = new Term[]{inst.u, 
                beforeLoopUpdate, 
                anonUpdate, 
                variantUpdate};
        final Term uAnonInv 
        = TB.applySequential(uAnon, TB.and(invTerm, reachableOut));
        final Term uAnonInvVariantNonNeg
        = TB.applySequential(uAnon, TB.and(new Term[]{invTerm, 
                reachableOut, 
                variantNonNeg}));

        final Term anonLoopHeap = loopHeap;
        final Term anonAssumption = assumption;
        final Term postAssumption 
        = TB.applySequential(new Term[]{inst.u, beforeLoopUpdate}, 
                TB.and(anonAssumption,TB.apply(anonUpdate,uAnonInv)));
        final AnonUpdateData anonUpdateAndHeap
        = new AnonUpdateData(anonAssumption, anonUpdate, wellFormedAnon, anonLoopHeap);

        // prepare information flow analysis
        Term contractLoopApplPredTerm =
            storeInvInPredAndGenInfoFlowTaclet(inst,
                    anonUpdateAndHeap,
                    TB.var(localIns),
                    TB.var(localOuts),
                    goal, services);

        //"Invariant Initially Valid":
        // \replacewith (==> inv );
        initGoal.changeFormula(new SequentFormula(
                TB.apply(inst.u, 
                        TB.and(variantNonNeg, 
                                TB.and(invTerm, reachableState)))),
                                ruleApp.posInOccurrence());

        //"Body Preserves Invariant":
        // \replacewith (==>  #atPreEqs(anon1) 
        //                       -> #introNewAnonUpdate(#modifies, #locDepFunc(anon1, \[{.. while (#e) #s ...}\]post) & inv -> 
        //                         (\[{ method-frame(#ex):{#typeof(#e) #v1 = #e;} }\]#v1=TRUE ->
        //                          #whileInvRule(\[{.. while (#e) #s ...}\]post, 
        //                               #locDepFunc(anon1, \[{.. while (#e) #s ...}\]post) & inv)),anon1));
        bodyGoal.addFormula(new SequentFormula(wellFormedAnon), 
                true, 
                false);		

        bodyGoal.addFormula(new SequentFormula(uAnonInvVariantNonNeg), 
                true, 
                false);

        final WhileInvRule wir 
        = (WhileInvRule) AbstractTermTransformer.WHILE_INV_RULE;
        SVInstantiations svInst 
        = SVInstantiations.EMPTY_SVINSTANTIATIONS.replace(
                null, 
                null, 
                inst.innermostExecutionContext, 
                null, 
                services);
        for(SchemaVariable sv : wir.neededInstantiations(inst.loop, svInst)) {
            assert sv instanceof ProgramSV;
            svInst = svInst.addInteresting(sv, 
                    (Name) new ProgramElementName(sv.name().toString()), 
                    services);
        }

        final Term invTerm2;
        final StrategyProperties props = goal.proof().getSettings().getStrategySettings().getActiveStrategyProperties();
        final boolean queryTreatmenIsOn = props.getProperty(StrategyProperties.QUERY_OPTIONS_KEY)==StrategyProperties.QUERY_ON;
        if(queryTreatmenIsOn || 
                props.getProperty(StrategyProperties.QUERY_OPTIONS_KEY)==StrategyProperties.QUERY_RESTRICTED){
            invTerm2 = QueryExpand.INSTANCE.evaluateQueries(services, invTerm, true, queryTreatmenIsOn); //chrisg
        }else{
            invTerm2 = invTerm;
        }

        Term bodyTerm = TB.tf().createTerm(wir, 
                inst.progPost,
                TB.and(new Term[]{invTerm2,
                        frameCondition,
                        variantPO}));
        bodyTerm = wir.transform(bodyTerm, svInst, services);
        final Term guardTrueBody = TB.box(guardJb, 
                TB.imp(guardTrueTerm, bodyTerm)); 

        bodyGoal.changeFormula(new SequentFormula(TB.applySequential(
                uBeforeLoopDefAnonVariant, 
                guardTrueBody)), 
                ruleApp.posInOccurrence());

        // "Use Case":
        // \replacewith (==> #introNewAnonUpdate(#modifies, inv ->
        // (\[{ method-frame(#ex):{#typeof(#e) #v1 = #e;} }\]
        // (#v1=FALSE -> \[{.. ...}\]post)),anon2))
        useGoal.addFormula(new SequentFormula(wellFormedAnon), 
                true, 
                false);		
        useGoal.addFormula(new SequentFormula(uAnonInv), true, false);
        useGoal.addFormula(new SequentFormula(postAssumption), // TODO: Is this correct? 
                true, 
                false);
        useGoal.addFormula(new SequentFormula(contractLoopApplPredTerm),
                true,
                false);

        Term restPsi = TB.prog((Modality)inst.progPost.op(),
                JavaTools.removeActiveStatement(
                        inst.progPost.javaBlock(), 
                        services), 
                        inst.progPost.sub(0));
        Term guardFalseRestPsi = TB.box(guardJb, 
                TB.imp(guardFalseTerm, restPsi));
        useGoal.changeFormula(new SequentFormula(TB.applySequential(
                uAnon,
                guardFalseRestPsi)), 
                ruleApp.posInOccurrence());
        return result;
    }
    
    /**
     * Store invariant of the loop invocation and generate information
     * flow taclet.
     */
    private Term storeInvInPredAndGenInfoFlowTaclet(final Instantiation inst,
                                                        final AnonUpdateData anonUpdateAndHeap,
                                                        final ImmutableList<Term> localIns,
                                                        final ImmutableList<Term> localOuts,
                                                        final Goal goal,
                                                        final Services services) {
        /*LoopInvariantApplicationData appData =
                new LoopInvariantApplicationData(inst.selfTerm, localIns,                                                 
                                                 TB.getBaseHeap(services),
                                                 localOuts,
                                                 anonUpdateAndHeap.loopHeap);*/
        ProofObligationVars appData =
            new ProofObligationVars(inst.selfTerm, null, localIns,
                                    localOuts, null, null,
                                    null, null,
                                    TB.getBaseHeap(services),
                                    anonUpdateAndHeap.loopHeap, "", services);
        IProgramMethod pm = JavaTools.getInnermostMethodFrame(inst.progPost.javaBlock(), 
                services).getProgramMethod();
        BasicPOSnippetFactory f =
            POSnippetFactory.getBasicFactory(inst.inv, appData, services);
        final Term loopInvariantApplPredTerm =
            f.create(BasicPOSnippetFactory.Snippet.METHOD_CALL_RELATION); // Different Snippet?
        final Term updatedLoopInvariantApplPredTerm =
            TB.apply(inst.u, loopInvariantApplPredTerm);
        
        final Function loopInvariantApplPred = (Function)loopInvariantApplPredTerm.op();
        final Taclet informationFlowContractLoopApp =
                genInfFlowContractLoopApplTaclet(inst.inv, loopInvariantApplPred, appData, pm,
                                             inst.u, services);
        goal.addTaclet(informationFlowContractLoopApp,
                       SVInstantiations.EMPTY_SVINSTANTIATIONS, true);
        return updatedLoopInvariantApplPredTerm;
        
        
        //final Function contLoopApplPred = generateContLoopApplPredicate(inst, appData, pm,
        //                                                        services);
        //final Term contractLoopApplPredTerm =
        //    TB.apply(inst.u, 
        //        instantiateContApplPredicate(contLoopApplPred, appData, pm));
        //final Taclet informationFlowContractLoopApp =
        //        genInfFlowContractLoopApplTaclet(contLoopApplPred, inst.inv, appData, pm, services);
        //goal.addTaclet(informationFlowContractLoopApp,
        //               SVInstantiations.EMPTY_SVINSTANTIATIONS, true);        
        //return contractLoopApplPredTerm;
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
    
    
    /*private Function generateContLoopApplPredicate(Instantiation inst,
            LoopInvariantApplicationData appData,
            IProgramMethod pm,
            Services services) {
        String nameString =
            MiscTools.toValidTacletName(inst.loop.getBody() +
                    inst.loop.getGuardExpression().toString() +
                    inst.innermostExecutionContext +
                    inst.inv
                    + "::" + inst.loop + "__LOOP").toString();
        final Name name = new Name(nameString);
        Function pred = (Function) services.getNamespaces().functions().lookup(
                name);
        if (pred == null) {
            // Arguments: local variables, heapAtPre, heapAtPost
            int length = appData.localIns.size() + appData.localOuts.size() + 2;            
            // Arguments: + self            
            if(!pm.isStatic()) {
                length++;
            }            
            Sort[] predArgSorts =
                new Sort[length];

            int i = 0;            
            // type of self
            if(!pm.isStatic()) {
                predArgSorts[i++] = inst.selfTerm.sort();
            }            
            // types of local variables (in)
            for(Term t : appData.localIns){
                predArgSorts[i++] = t.sort();
            }
            // type of heapAtPre
            predArgSorts[i++] = TB.getBaseHeap(services).sort();
            // types of local variables (out)
            for(Term t : appData.localOuts){
                predArgSorts[i++] = t.sort();
            }
            // type of heapAtPost
            predArgSorts[i++] = TB.getBaseHeap(services).sort();

            pred = new Function(name, Sort.FORMULA, predArgSorts);
            services.getNamespaces().functions().addSafely(pred);
        }
        return pred;
    }*/


    /*private Term instantiateContApplPredicate(Function pred,
            LoopInvariantApplicationData appData,
            IProgramMethod pm) {
        Sort[] predArgSorts = new Sort[pred.argSorts().size()];
        pred.argSorts().toArray(predArgSorts);
        Term[] predArgs = new Term[predArgSorts.length];        

        int i = 0;        

        if(!pm.isStatic()) {
            // self
            predArgs[i++] = appData.self;
        }        
        // local variables (in)
        for(Term t : appData.localIns){
            predArgSorts[i] = t.sort();
            predArgs[i++] = t;
        }        
        // local variables (out)
        for(Term t : appData.localOuts){
            predArgSorts[i] = t.sort();
            predArgs[i++] = t;
        }        
        // heapAtPre
        predArgs[i++] = appData.heapAtPre;        
        // heapAtPost
        predArgs[i++] = appData.heapAtPost;

        return TB.func(pred, predArgs);
    }*/


    private ProofObligationVars generateLoopApplicationDataSVs(Function pred,
            String schemaPrefix,
            ProofObligationVars appData,
            IProgramMethod pm,
            Services services) {        
        Sort[] predArgSorts = new Sort[pred.argSorts().size()];
        pred.argSorts().toArray(predArgSorts);        
        //final int numLocalIns = appData.params.size();
        ImmutableList<Term> localInsSVs = ImmutableSLList.<Term>nil();
        //final int numLocalOuts = appData.results.size();
        ImmutableList<Term> localOutsSVs = ImmutableSLList.<Term>nil();

        int i = 0;
        Term selfAtPreSV;
        if(!pm.isStatic()) {
            selfAtPreSV = createTermSV(schemaPrefix + "_self",
                    predArgSorts[i], services);
            i++;
        } else {
            selfAtPreSV = null;            
        }
        int j = 0;        
        for(Term t : appData.params){
            predArgSorts[i] = t.sort();
            localInsSVs.append(createTermSV(schemaPrefix + "_param_" +
                    (j + 1), predArgSorts[i],
                    services));
            i++;
            j++;
        }        
        Term heapAtPreSV = createTermSV(schemaPrefix + "_heapAtPre",
                predArgSorts[i], services);
        i++;
        j = 0;
        localOutsSVs = ImmutableSLList.<Term>nil();
        if (!pm.isVoid() && !pm.isConstructor()) {
            for(Term t : appData.results){
                predArgSorts[i] = t.sort();
                localOutsSVs.append(createTermSV(schemaPrefix + "_res_" +
                        (j + 1), predArgSorts[i],
                        services));
                i++;
                j++;
            }
        }
        Term heapAtPostSV = createTermSV(schemaPrefix + "_heapAtPost",
                predArgSorts[i], services);
        i++;

        return new ProofObligationVars(selfAtPreSV, selfAtPreSV, localInsSVs, localOutsSVs,
                localOutsSVs, TB.ff(), TB.ff(), heapAtPreSV,
                heapAtPreSV, heapAtPostSV, "", services);
    }

    private Taclet genInfFlowContractLoopApplTaclet(LoopInvariant loopInv,
            Function contractLoopApplPred,
            ProofObligationVars appData,
            IProgramMethod pm,
            Term stateUpdate,
            Services services) {
        Name tacletName =
            MiscTools.toValidTacletName("use information flow loop contract for "
                    + contractLoopApplPred.name());

//        LoopInvariantApplicationData schemaDataFind = generateLoopApplicationDataSVs(
//                contractLoopApplPred, "find", appData, pm, services);
//        LoopInvariantApplicationData schemaDataAssumes = generateLoopApplicationDataSVs(
//                contractLoopApplPred, "assumes", appData, pm, services);        
        ProofObligationVars schemaDataFind = generateLoopApplicationDataSVs(
                contractLoopApplPred, "find", appData, pm, services);
        ProofObligationVars schemaDataAssumes = generateLoopApplicationDataSVs(
                contractLoopApplPred, "assumes", appData, pm, services);
        
        
        /*generateLoopApplicationDataSVs(Function pred,
                String schemaPrefix,
                ProofObligationVars appData,
                IProgramMethod pm,
                Services services)*/
        
        
        BasicPOSnippetFactory fFind =
            POSnippetFactory.getBasicFactory(loopInv, schemaDataFind, services);
        BasicPOSnippetFactory fAssumes =
            POSnippetFactory.getBasicFactory(loopInv, schemaDataAssumes, services);
        
//        Term schemaFind = instantiateContApplPredicate(contractLoopApplPred,
//                schemaDataFind, pm);
//        Term schemaAssumes = instantiateContApplPredicate(contractLoopApplPred,
//                schemaDataAssumes, pm);
        
        Term schemaFind = // Different Snippet?
            TB.apply(stateUpdate, fFind.create(BasicPOSnippetFactory.Snippet.METHOD_CALL_RELATION));
        Term schemaAssumes = // Different Snippet?
            TB.apply(stateUpdate, fAssumes.create(BasicPOSnippetFactory.Snippet.METHOD_CALL_RELATION));
        
        /*ImmutableSet<InformationFlowContract> ifContracts =
            getInfromFlowContracts(pm, services);*/
        // Why should we have multiple loop invariants?
        Term schemaContApps =
            buildContractApplication(loopInv, schemaDataFind,
                    schemaDataAssumes, services);

        /*Term schemaContApps = InformationFlowContractPO.buildContractApplication(
                loopInv, schemaDataFind, schemaDataAssumes, services);
        Term schemaContPrev = InformationFlowContractPO.buildContractApplication(
                loopInv, schemaDataFind, schemaDataAssumes, services);*/ // TODO: Here we
        //want the new formula
        //(Lemma 1 slightly changed)

        //create sequents
        Sequent assumesSeq = Sequent.createAnteSequent(
                new Semisequent(new SequentFormula(schemaAssumes)));
        Sequent axiomSeq = Sequent.createAnteSequent(
                new Semisequent(new SequentFormula(schemaContApps)));
//        Sequent bodySeq = Sequent.createSuccSequent(
//                new Semisequent(new SequentFormula(schemaContPrev)));

        //create taclet
        RewriteTacletBuilder tacletBuilder = new RewriteTacletBuilder(); // TODO: create new branch for body preserves
        // -> Not exactly clear. Make a new predicate with changed formula?
        tacletBuilder.setName(tacletName);
        tacletBuilder.setFind(schemaFind); // TODO: is this correct? has to match only in the antecedent!
        tacletBuilder.setIfSequent(assumesSeq); //concerning above comment -> write eMail to remind Christoph!
        RewriteTacletGoalTemplate goal =
            new RewriteTacletGoalTemplate(axiomSeq,
                    ImmutableSLList.<Taclet>nil(),
                    schemaFind);
        tacletBuilder.addTacletGoalTemplate(goal);
//        RewriteTacletGoalTemplate goal2 =
//            new RewriteTacletGoalTemplate(bodySeq,
//                    ImmutableSLList.<Taclet>nil(),
//                    schemaFind);
//        tacletBuilder.addTacletGoalTemplate(goal2);
        tacletBuilder.addRuleSet(new RuleSet(new Name("information_flow_loop_invariant_appl")));
        tacletBuilder.setSurviveSmbExec(true);
        return tacletBuilder.getTaclet();
    }


    @Override
    public LoopInvariantBuiltInRuleApp createApp(PosInOccurrence pos) {
        return new LoopInvariantBuiltInRuleApp(this, pos);
    }
    
    public static Term buildContractApplication(
            LoopInvariant loopInv,
            ProofObligationVars contAppData,
            ProofObligationVars contAppData2,
            Services services) {
        InfFlowPOSnippetFactory f =
            POSnippetFactory.getInfFlowFactory(loopInv, contAppData,
                    contAppData2, services);
        return f.create(InfFlowPOSnippetFactory.Snippet.INF_FLOW_CONTRACT_APPL);
    }
    
    /*private static Term buildInputRelation(LoopInvariant loopInv,
            IFProofObligationVars vs,
            ImmutableList<Term> referenceLocSet1,
            ImmutableList<Term> referenceLocSet2,
            Services services) {
        final Term mainInputEqRelation =
            buildMainInputEqualsRelation(loopInv, referenceLocSet1,
                    referenceLocSet2, vs, services);        

        ImmutableList<Term> inputRelations =
            ImmutableSLList.<Term>nil();
        inputRelations = inputRelations.append(mainInputEqRelation);

        return TB.and(inputRelations);
    }*/
    
    /*private static Term buildOutputRelation(LoopInvariant loopInv,
            IFProofObligationVars vs,
            ImmutableList<Term> referenceLocSet1,
            ImmutableList<Term> referenceLocSet2,
            Services services) {
        Term mainEqRelation =
            buildMainOutputEqualsRelation(loopInv, referenceLocSet1,
                    referenceLocSet2, vs, services);
        ImmutableList<Term> outputRelations = ImmutableSLList.<Term>nil();
        outputRelations = outputRelations.append(mainEqRelation);
        return TB.and(outputRelations);
    }*/
    
    /*private static Term buildInputOutputRelations(LoopInvariant loopInv,
            IFProofObligationVars vs,
            Services services) {
        ImmutableList<ImmutableList<Term>> respectsAtPre1 =
            loopInv.getRespects(vs.c1.heapAtPre, vs.c1.self,
                    vs.c1.params, services);
        ImmutableList<ImmutableList<Term>> respectsAtPre2 =
            loopInv.getRespects(vs.c2.heapAtPre, vs.c2.self,
                    vs.c2.params, services);
        ImmutableList<ImmutableList<Term>> respectsAtPost1 =
            loopInv.getRespects(vs.c1.heapAtPost, vs.c1.selfAtPost,
                    vs.c1.params, services);
        ImmutableList<ImmutableList<Term>> respectsAtPost2 =
            loopInv.getRespects(vs.c2.heapAtPost, vs.c2.selfAtPost,
                    vs.c2.params, services);


        ImmutableList<Term> inputOutputRelations = ImmutableSLList.<Term>nil();

        Iterator<ImmutableList<Term>> respectsAtPre2It = respectsAtPre2.iterator();
        Iterator<ImmutableList<Term>> respectsAtPost1It = respectsAtPost1.iterator();
        Iterator<ImmutableList<Term>> respectsAtPost2It = respectsAtPost2.iterator();
        for (ImmutableList<Term> referenceLocSetAtPre1 : respectsAtPre1) {
            ImmutableList<Term> referenceLocSetAtPre2 = respectsAtPre2It.next();
            ImmutableList<Term> referenceLocSetAtPost1 = respectsAtPost1It.next();
            ImmutableList<Term> referenceLocSetAtPost2 = respectsAtPost2It.next();
            Term inputOutputRelation =
                buildInputOutputRelation(loopInv, referenceLocSetAtPre1,
                        referenceLocSetAtPre2,
                        referenceLocSetAtPost1,
                        referenceLocSetAtPost2, vs, services);
            inputOutputRelations =
                inputOutputRelations.append(inputOutputRelation);
        }

        return TB.and(inputOutputRelations);
    }*/
    
    /*private static Term buildInputOutputRelation(LoopInvariant loopInv,
            ImmutableList<Term> referenceLocSetAtPre1,
            ImmutableList<Term> referenceLocSetAtPre2,
            ImmutableList<Term> referenceLocSetAtPost1,
            ImmutableList<Term> referenceLocSetAtPost2,
            IFProofObligationVars vs,
            Services services) {
        Term inputRelation =
            buildInputRelation(loopInv, vs, referenceLocSetAtPre1,
                    referenceLocSetAtPre2, services);
        Term outputRelation =
            buildOutputRelation(loopInv, vs, referenceLocSetAtPost1,
                    referenceLocSetAtPost2, services);

        return TB.imp(inputRelation, outputRelation);
    }*/
    
    /*private static Term buildMainInputEqualsRelation(LoopInvariant loopInv,
            ImmutableList<Term> referenceLocSet1,
            ImmutableList<Term> referenceLocSet2,
            IFProofObligationVars vs,
            Services services) {        
        Term[] eqAtLocs = new Term[referenceLocSet1.size()];
        Iterator<Term> refLoc1It = referenceLocSet1.iterator();
        Iterator<Term> refLoc2It = referenceLocSet2.iterator();
        for(int i=0; i < eqAtLocs.length; i++) {
            Term refLoc1Term = refLoc1It.next();
            Term refLoc2Term = refLoc2It.next();
            //// hack ?
            //if(refLoc1Term.sort().name().equals(services.getTypeConverter().getLocSetLDT().name())) {
            //eqAtLocs[i] = TB.eqAtLocs(services,
            //vs.c1.heapAtPre,
            //TB.intersect(services, refLoc1Term,
            //    framingLocs1),
            //vs.c2.heapAtPre,
            //TB.intersect(services, refLoc2Term,
            //    framingLocs2));
            //} else {
            SearchVisitor[] search = new SearchVisitor[vs.c1.resultsAtPost.size()];
            int j = 0;
            for(Term resPost: vs.c1.resultsAtPost) {
                search[j] = new SearchVisitor(resPost);
                refLoc1Term.execPreOrder(search[j]);
                eqAtLocs[i] = TB.tt();
                if (!search[j].termFound) {
                    // refLocTerms which contain \result are not included in
                    // the precondition
                    eqAtLocs[i] = TB.and(eqAtLocs[i],TB.equals(refLoc1Term, refLoc2Term));
                } else {
                    eqAtLocs[i] = TB.and(eqAtLocs[i],TB.tt());
                }
                j++;
            }                
            //}
        }
        return TB.and(eqAtLocs);
    }*/
    
    /*private static Term buildMainOutputEqualsRelation(LoopInvariant loopInv,
            ImmutableList<Term> referenceLocSet1,
            ImmutableList<Term> referenceLocSet2,
            IFProofObligationVars vs,
            Services services) {        
        Term framingLocs1 =
            loopInv.getModifies(vs.c1.self, loopInv.getInternalAtPres(), services); //vs.c1.heapAtPre?
        Term framingLocs2 =
            loopInv.getModifies(vs.c2.self, loopInv.getInternalAtPres(), services); //vs.c2.heapAtPre?

        Term[] eqAtLocs = new Term[referenceLocSet1.size()];
        Iterator<Term> refLoc1It = referenceLocSet1.iterator();
        Iterator<Term> refLoc2It = referenceLocSet2.iterator();
        for(int i=0; i < eqAtLocs.length; i++) {
            Term refLoc1Term = refLoc1It.next();
            Term refLoc2Term = refLoc2It.next();
            // TOTO: hack ?
            //if(refLoc1Term.sort().name().equals(services.getTypeConverter().getLocSetLDT().name())) {
            //eqAtLocs[i] = TB.eqAtLocsPost(services,
            //vs.c1.heapAtPre,
            //vs.c1.heapAtPost,
            //TB.intersect(services, refLoc1Term,
            //       framingLocs1),
            //vs.c2.heapAtPre,
            //vs.c2.heapAtPost,
            //TB.intersect(services, refLoc2Term,
            //       framingLocs2));
            //} else {
            eqAtLocs[i] = TB.equals(refLoc1Term, refLoc2Term);
            //}
        }
        return TB.and(eqAtLocs);
    }*/
    
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

        public final Term assumption, anonUpdate, anonHeap, loopHeap;


        public AnonUpdateData(Term assumption,
                              Term anonUpdate,
                              Term anonHeap,
                              Term loopHeap) {
            this.assumption = assumption;
            this.anonUpdate = anonUpdate;
            this.loopHeap = loopHeap;
            this.anonHeap = anonHeap;
        }
    }
}