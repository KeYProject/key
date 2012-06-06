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

import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.List;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSet;
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
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.rule.metaconstruct.WhileInvRule;
import de.uka.ilkd.key.speclang.LoopInvariant;
import de.uka.ilkd.key.speclang.HeapContext;
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
         
	//collect self, execution context
	final MethodFrame innermostMethodFrame 
		= MiscTools.getInnermostMethodFrame(progPost.javaBlock(), 
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


    
    /**
     * @return (anon update, anon heap)
     */
    private Pair<Term,Term> createAnonUpdate(LocationVariable heap,
	    			While loop, 
	    			Term mod,
	    			ImmutableSet<ProgramVariable> localOuts,
	    			Services services) {
	final HeapLDT heapLDT = services.getTypeConverter().getHeapLDT();
	final Name anonHeapName = new Name(TB.newName(services, "anon_"+heap.name()+"_loop"));
	final Function anonHeapFunc = new Function(anonHeapName,
					     heapLDT.targetSort());
	services.getNamespaces().functions().addSafely(anonHeapFunc);
	final Term anonHeapTerm = TB.func(anonHeapFunc);
	
	// check for strictly pure loops
	Term anonUpdate;
	if(TB.lessThanNothing().equals(mod)) {
	    anonUpdate = TB.skip();
	} else {
	    anonUpdate = TB.anonUpd(heap, services, mod, anonHeapTerm);
	}
	
	//local output vars
	if(localOuts != null) {
	    for(ProgramVariable pv : localOuts) {
	        final String anonFuncName 
	    	    = TB.newName(services, pv.name().toString());
	        final Function anonFunc 
	    	    = new Function(new Name(anonFuncName), pv.sort());
	        services.getNamespaces().functions().addSafely(anonFunc);
	        final Term elemUpd = TB.elementary(services, 
	                (LocationVariable)pv, 
	                TB.func(anonFunc));
	        anonUpdate = TB.parallel(anonUpdate, elemUpd);
	    }
	}
	return new Pair<Term,Term>(anonUpdate, anonHeapTerm);
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
        SourceElement activeStatement = MiscTools
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
	
    final boolean transaction = ((Modality)inst.progPost.op()).transaction(); 

    final Map<LocationVariable,Term> atPres = inst.inv.getInternalAtPres();
    final HeapContext hc = inst.inv.getHeapContext(transaction);
    final List<LocationVariable> modHeaps = hc.getModHeaps(services);

//    final Term transactionInv = transaction ? inst.inv.getInvariant(inst.selfTerm, atPres, services) : null;

    final Term regularInv = inst.inv.getInvariant(inst.selfTerm, atPres, services, false);

    final Term invTerm;
    if(transaction) {
      final Term transactionInv = inst.inv.getInvariant(inst.selfTerm, atPres, services, true);
      if(transactionInv != null) {
        invTerm = TB.and(regularInv, transactionInv);
      }else{
        invTerm = regularInv;
      }
    }else{
      invTerm = regularInv;
    }

//    final Term s = atPres.get(TermBuilder.SAVED_HEAP_NAME);
    final Map<LocationVariable,Term> mods = new LinkedHashMap<LocationVariable,Term>();
    for(LocationVariable heap : modHeaps) {
      final Term m = inst.inv.getModifies(heap, inst.selfTerm, atPres, services);
      mods.put(heap, m);
    }

//    final Term mod = inst.inv.getModifies(TermBuilder.BASE_HEAP_NAME, inst.selfTerm, 
//					      atPres, 
//					      services);
	// This on the other hand should never be null
//    final Term modBackup = inst.inv.getModifies(TermBuilder.SAVED_HEAP_NAME,inst.selfTerm, 
//            atPres, 
//            services);

//  atPres.put(TermBuilder.SAVED_HEAP_NAME, null);
//  final Term regularInv = inst.inv.getInvariant(inst.selfTerm, atPres, services);
   // NOTE even when a transaction is on, the transactionInv can still be null (no loop_invariant_transaction given)
//	final Term invTerm  = transactionInv != null ?
//	     TB.and(regularInv, transactionInv) : regularInv;
	final Term variant = inst.inv.getVariant(inst.selfTerm, 
						 atPres, 
						 services);
//	atPres.put(TermBuilder.SAVED_HEAP_NAME, s);
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
//        final Map<Term,Term> savedToBeforeLoop = new HashMap<Term,Term>();
//	final Map<Term,Term> normalToBeforeLoop = new HashMap<Term,Term>();

        final Map<LocationVariable,Map<Term,Term>> heapToBeforeLoop = new LinkedHashMap<LocationVariable,Map<Term,Term>>();

        for(LocationVariable heap : modHeaps) {
          heapToBeforeLoop.put(heap, new HashMap<Term,Term>());
          final LocationVariable lv = TB.heapAtPreVar(services, heap.name()+"BeforeLoop", true);
   	  services.getNamespaces().programVariables().addSafely(lv);
          final Term u = TB.elementary(services, lv, TB.var(heap));
          if(beforeLoopUpdate == null) {
             beforeLoopUpdate = u;
          }else{
             beforeLoopUpdate = TB.parallel(beforeLoopUpdate, u);
          }
          heapToBeforeLoop.get(heap).put(TB.var(heap), TB.var(lv));
//          if(h.equals(TermBuilder.SAVED_HEAP_NAME)) {
//	    savedToBeforeLoop.put(TB.heap(h, services), TB.var(lv));
//          }else{
//	    normalToBeforeLoop.put(TB.heap(h, services), TB.var(lv));
//          }
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

        Term anonUpdate = null;
        Term wellFormedAnon = null;
        Term frameCondition = null;
        Term reachableState = reachableIn;
        for(LocationVariable heap : modHeaps) {
	  final Pair<Term,Term> tAnon 
	      = createAnonUpdate(heap, inst.loop, mods.get(heap), null, services);
          if(anonUpdate == null) {
            anonUpdate = tAnon.first;
          }else{
            anonUpdate = TB.parallel(anonUpdate, tAnon.first);
          }
          if(wellFormedAnon == null) {
            wellFormedAnon = TB.wellFormed(tAnon.second, services);
          }else{
            wellFormedAnon = TB.and(wellFormedAnon, TB.wellFormed(tAnon.second, services));
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

//	final Pair<Term,Term> anonUpdateAndHeap 
//		= createAnonUpdate(TermBuilder.BASE_HEAP_NAME, inst.loop, mod, localOuts, services);
//	final Term anonUpdate;
//	final Term anonHeapWellFormed;
//	if(transaction) {
//	    final Pair<Term,Term> anonUpdateAndHeapSaved  
//	      = createAnonUpdate(TermBuilder.SAVED_HEAP_NAME, inst.loop, modBackup, null, services);
//	  anonUpdate = TB.parallel(anonUpdateAndHeap.first, anonUpdateAndHeapSaved.first);
//	  anonHeapWellFormed   = TB.and(TB.wellFormed(services, anonUpdateAndHeap.second), TB.wellFormed(services, anonUpdateAndHeapSaved.second));
//	}else{
//	  anonUpdate = anonUpdateAndHeap.first;
//	  anonHeapWellFormed   = TB.wellFormed(services, anonUpdateAndHeap.second);	    
//	}

	// special case frame condition for strictly pure loops
//	final Term normalFrameCondition;
//	if(TB.lessThanNothing().equals(mod)) {
//	    normalFrameCondition = TB.frameStrictlyEmpty(services, TB.heap(TermBuilder.BASE_HEAP_NAME, services), normalToBeforeLoop); 
//	} else {
//	    normalFrameCondition = TB.frame(services, TB.heap(TermBuilder.BASE_HEAP_NAME, services),
//               normalToBeforeLoop, 
//               mod);
//	}
//	final Term transactionFrameCondition = transaction ?
//	          TB.frame(services, TB.heap(TermBuilder.SAVED_HEAP_NAME,services), savedToBeforeLoop, modBackup)
//	        : null;
        
//	final Term frameCondition = transactionFrameCondition != null ?
//	        TB.and(normalFrameCondition,transactionFrameCondition) : normalFrameCondition;
	
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

	Term restPsi = TB.prog((Modality)inst.progPost.op(),
			       MiscTools.removeActiveStatement(
				       	inst.progPost.javaBlock(), 
					services), 
                               inst.progPost.sub(0));
	Term guardFalseRestPsi = TB.box(guardJb, 
					TB.imp(guardFalseTerm, restPsi));
	useGoal.changeFormula(new SequentFormula(TB.applySequential(
							uAnon,
							guardFalseRestPsi)), 
                              ruleApp.posInOccurrence());
        hc.reset();
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


}
