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
import de.uka.ilkd.key.proof.init.BlockExecutionPO;
import de.uka.ilkd.key.proof.init.ContractPO;
import de.uka.ilkd.key.proof.init.InfFlowContractPO;
import de.uka.ilkd.key.proof.init.SymbolicExecutionPO;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.rule.metaconstruct.WhileInvRule;
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
	inv.setTarget(innermostMethodFrame.getProgramMethod());
	final Term selfTerm = innermostMethodFrame == null
	                      ? null
	                      : MiscTools.getSelfTerm(innermostMethodFrame, 
	                	      		      services);
	final ExecutionContext innermostExecutionContext 
		= innermostMethodFrame == null 
		  ? null
		  : (ExecutionContext) 
		          innermostMethodFrame.getExecutionContext();
	inv.setExecutionContext(innermostExecutionContext);

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
     * @return (assumption, anon update, anon heap)
     */    
    private static AnonUpdateData createAnonUpdate(LocationVariable heap,
	    			LoopInvariant loop_inv, 
	    			Term mod,
	    			Services services) {
        assert loop_inv != null;
        
	final HeapLDT heapLDT = services.getTypeConverter().getHeapLDT();
	final Name loopHeapName = new Name(TB.newName(services, heap+"After_"+ loop_inv.getName()));
        final Function loopHeapFunc = new Function(loopHeapName,
                                             heapLDT.targetSort(), true);
        services.getNamespaces().functions().addSafely(loopHeapFunc);
        final Term loopHeap = TB.func(loopHeapFunc);
	final Name anonHeapName = new Name(TB.newName(services, "anon_"+heap+"_" + loop_inv.getName()));
	final Function anonHeapFunc = new Function(anonHeapName,heap.sort(), true);
	services.getNamespaces().functions().addSafely(anonHeapFunc);
	final Term anonHeap = TB.func(anonHeapFunc);	
	
	// check for strictly pure loops
	final Term anonUpdate;
	if(TB.lessThanNothing().equals(mod)) {
	    anonUpdate = TB.skip();
	} else {
	    anonUpdate = TB.anonUpd(heap, services, mod, anonHeap);
	}
	
	final Term assumption =
                TB.equals(TB.anon(services, TB.var(heap), mod, anonHeap),
                          loopHeap);
	
	return new AnonUpdateData(assumption, anonUpdate, loopHeap, TB.getBaseHeap(services), anonHeap);
    }
    
    /*private Term createTermSV(String svName,
            Sort predArgSort,
            Services services) {
        Name name = services.getVariableNamer().getTemporaryNameProposal(svName);
        return TB.var(SchemaVariableFactory.createTermSV(name, predArgSort));
    }*/
    
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
    public ImmutableList<Goal> apply(Goal goal, Services services, RuleApp ruleApp)
            throws RuleAbortException {
        
        final KeYJavaType booleanKJT = services.getTypeConverter().getBooleanType();
        final KeYJavaType intKJT =
                services.getJavaInfo().getPrimitiveKeYJavaType(PrimitiveType.JAVA_INT);
        
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

        Term beforeLoopUpdate = null;

        final Map<LocationVariable,Map<Term,Term>> heapToBeforeLoop = new LinkedHashMap<LocationVariable,Map<Term,Term>>();

        for(LocationVariable heap : heapContext) {
            heapToBeforeLoop.put(heap, new LinkedHashMap<Term,Term>());
            final LocationVariable lv = TB.heapAtPreVar(services, heap+"Before_"+inst.inv.getName(), heap.sort(), true);
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
            = TB.newName(services, pv.name().toString() + "Before_" + inst.inv.getName());
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
        Term anonAssumption = null;
        Term wellFormedAnon = null;
        Term frameCondition = null;
        Term reachableState = null;
        ImmutableList<AnonUpdateData> anonUpdateDatas =
                ImmutableSLList.<AnonUpdateData>nil();
        for(LocationVariable heap : heapContext) {
            final AnonUpdateData tAnon
            = createAnonUpdate(heap, inst.inv, mods.get(heap), services);
            anonUpdateDatas = anonUpdateDatas.append(tAnon);
            if(anonAssumption == null) {
                anonAssumption = tAnon.assumption;
            } else {
                anonAssumption = TB.and(anonAssumption,tAnon.assumption);
            }
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
            if(reachableState == null) {
                reachableState = TB.wellFormed(heap, services);
              }else{
                reachableState = TB.and(reachableState, TB.wellFormed(heap, services));
              }
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

        final Term postAssumption 
        = TB.applySequential(new Term[]{inst.u, beforeLoopUpdate}, 
                TB.and(anonAssumption,TB.apply(anonUpdate,uAnonInv)));
        
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
        
        final ContractPO po 
        = services.getSpecificationRepository()
                  .getPOForProof(goal.proof());

        if (po instanceof InfFlowContractPO ||
            po instanceof SymbolicExecutionPO ||
            po instanceof BlockExecutionPO) {
        // prepare information flow analysis
        /*Term contractLoopApplPredTerm =
                storeInvInPredAndGenInfoFlowTaclet(inst,
                        anonUpdateAndHeap,
                        TB.var(localIns),
                        TB.var(localOuts),
                        goal, services);*/
        assert anonUpdateDatas.size() == 1; // information flow extension is at
                                            // the moment not compatible with
                                            // the non-base-heap setting
        final AnonUpdateData anonUpdateData = anonUpdateDatas.head();

        InfFlowLoopInvariantTacletBuilder ifInvariantBuilder =
                new InfFlowLoopInvariantTacletBuilder(services);
        ifInvariantBuilder.setInvariant(inst.inv);
        ifInvariantBuilder.setContextUpdate(inst.u);
        ifInvariantBuilder.setHeapAtPre(anonUpdateData.loopHeapAtPre);
        ifInvariantBuilder.setHeapAtPost(anonUpdateData.loopHeap);
        ifInvariantBuilder.setSelf(inst.selfTerm);
        ifInvariantBuilder.setLocalIns(TB.var(localIns));
        ifInvariantBuilder.setLocalOuts(TB.var(localOuts));


        // generate information flow invariant application predicate
        // and associated taclet
        Term contractApplPredTerm =
                ifInvariantBuilder.buildContractApplPredTerm();
        Taclet informationFlowInvariantApp =
                ifInvariantBuilder.buildContractApplTaclet();
        
        // add term and taclet to post goal
        useGoal.addFormula(new SequentFormula(contractApplPredTerm),
                true,
                false);
        useGoal.addTaclet(informationFlowInvariantApp,
                SVInstantiations.EMPTY_SVINSTANTIATIONS, true);        
        }

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
    /*private Term storeInvInPredAndGenInfoFlowTaclet(final Instantiation inst,
                                                        final AnonUpdateData anonUpdateAndHeap,
                                                        final ImmutableList<Term> localIns,
                                                        final ImmutableList<Term> localOuts,
                                                        final Goal goal,
                                                        final Services services) {
        ProofObligationVars appData =
            new ProofObligationVars(inst.selfTerm, null, localIns,
                                    localOuts, null, null,
                                    null, null,
                                    TB.getBaseHeap(services),
                                    anonUpdateAndHeap.loopHeap, "", services);
        BasicPOSnippetFactory f =
            POSnippetFactory.getBasicFactory(inst.inv, appData, services);
        final Term loopInvariantApplPredTerm =
            f.create(BasicPOSnippetFactory.Snippet.LOOP_CALL_RELATION);
        final Term updatedLoopInvariantApplPredTerm =
            TB.apply(inst.u, loopInvariantApplPredTerm);
        
        final Function loopInvariantApplPred = (Function)loopInvariantApplPredTerm.op();
        final Taclet informationFlowContractLoopApp =
                genInfFlowContractLoopApplTaclet(inst.inv, loopInvariantApplPred, appData,
                                                 services);
        goal.addTaclet(informationFlowContractLoopApp,
                       SVInstantiations.EMPTY_SVINSTANTIATIONS, true);
        return updatedLoopInvariantApplPredTerm;
    }*/
    
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

        public final Term assumption, anonUpdate, anonHeap, loopHeap, loopHeapAtPre;


        public AnonUpdateData(Term assumption,
                              Term anonUpdate,
                              Term loopHeap,
                              Term loopHeapAtPre,
                              Term anonHeap) {
            this.assumption = assumption;
            this.anonUpdate = anonUpdate;
            this.loopHeap = loopHeap;
            this.loopHeapAtPre = loopHeapAtPre;
            this.anonHeap = anonHeap;
        }
    }
}