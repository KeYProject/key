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

import java.util.Collections;
import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;
import java.util.Vector;

import de.uka.ilkd.key.collection.ImmutableArray;
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
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.rule.metaconstruct.WhileInvRule;
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
    
    private Instantiation instantiate(Term focusTerm, Services services) {
	if(focusTerm == lastFocusTerm
	   && lastInstantiation.inv 
	       == services.getSpecificationRepository()
	                  .getLoopInvariant(lastInstantiation.loop)) {
	    return lastInstantiation;
	}

	//leading update?
	final Term u;
	final Term progPost;
	if(focusTerm.op() instanceof UpdateApplication) {
	    u = UpdateApplication.getUpdate(focusTerm);
	    progPost = UpdateApplication.getTarget(focusTerm);
	} else {
	    u = TB.skip();
	    progPost = focusTerm;
	}

	//focus (below update) must be modality term
	if(progPost.op() != Modality.BOX && progPost.op() != Modality.DIA
	    && progPost.op() != Modality.BOX_TRANSACTION && progPost.op() != Modality.DIA_TRANSACTION) {
	    return null;
	}

	//active statement must be while loop
	SourceElement activeStatement 
		= MiscTools.getActiveStatement(progPost.javaBlock());
	if(!(activeStatement instanceof While)) {
	    return null;
	}
	final While loop = (While) activeStatement;

	//an invariant must be present for the loop
	final LoopInvariant inv 
		= services.getSpecificationRepository().getLoopInvariant(loop);
	if(inv == null 
           || inv.getInvariant(inv.getInternalSelfTerm(), 
        	   	       inv.getInternalHeapAtPre(), null, 
			       services) == null
	   || (progPost.op() == Modality.DIA 
	       && inv.getVariant(inv.getInternalSelfTerm(), 
		       		 inv.getInternalHeapAtPre(), 
		       		 services) == null)) {
	    return null;
	}

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
    private Pair<Term,Term> createAnonUpdate(
	    			While loop, 
	    			Term mod,
	    			ImmutableSet<ProgramVariable> localOuts,
	    			Services services) {
	//heap
    // shortcut - localOuts == null means we create the anon-update for the savedHeap
    final boolean transaction = (localOuts == null);
	final HeapLDT heapLDT = services.getTypeConverter().getHeapLDT();
	final Name anonHeapName 
		= new Name(TB.newName(services, transaction ? "anonSavedHeap_loop" : "anonHeap_loop"));
	final Function anonHeapFunc = new Function(anonHeapName,
					     heapLDT.targetSort());
	services.getNamespaces().functions().addSafely(anonHeapFunc);
	final Term anonHeapTerm = TB.func(anonHeapFunc);
	
	// check for strictly pure loops
	Term anonUpdate;
	if(TB.lessThanNothing().equals(mod)) {
	    anonUpdate = TB.skip();
	} else {
	    anonUpdate = TB.anonUpd(services, mod, anonHeapTerm, transaction);
	}
	
	//local output vars
	if(!transaction) {
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
    
    
    
    //-------------------------------------------------------------------------
    //public interface
    //-------------------------------------------------------------------------

    @Override
    public boolean isApplicable(Goal goal, 
	    			PosInOccurrence pio) {
	//focus must be top level succedent
	if(pio == null || !pio.isTopLevel() || pio.isInAntec()) {
	    return false;
	}

	//instantiation must succeed
	Instantiation inst = instantiate(pio.subTerm(), 
		                         goal.proof().getServices());
	return inst != null;
    }

    
    @Override
    public ImmutableList<Goal> apply(Goal goal, Services services, RuleApp ruleApp) {
	final KeYJavaType booleanKJT = services.getTypeConverter()
	                                       .getBooleanType();
	final KeYJavaType intKJT 
		= services.getJavaInfo()
	                  .getPrimitiveKeYJavaType(PrimitiveType.JAVA_INT);
	//get instantiation
	Instantiation inst = instantiate(ruleApp.posInOccurrence().subTerm(), 
				         services);
    final boolean transaction = (inst.progPost.op() == Modality.DIA_TRANSACTION || inst.progPost.op() == Modality.BOX_TRANSACTION); 

    final Term heapAtMethodPre = inst.inv.getInternalHeapAtPre();
    final Term savedHeapAtMethodPre = inst.inv.getInternalSavedHeapAtPre();
    final Term regularInv = inst.inv.getInvariant(inst.selfTerm, heapAtMethodPre, null, services);
    final Term transactionInv = transaction ? inst.inv.getInvariant(inst.selfTerm, heapAtMethodPre, savedHeapAtMethodPre, services) : null;
    // NOTE even when a transaction is on, the transactionInv can still be null (no loop_invariant_transaction given)
	final Term invTerm  = transactionInv != null ?
	     TB.and(regularInv, transactionInv) : regularInv;
	final Term mod = inst.inv.getModifies(inst.selfTerm, 
					      heapAtMethodPre, null, 
					      services);
	// This on the other hand should never be null
    final Term modBackup = inst.inv.getModifies(inst.selfTerm, 
            heapAtMethodPre, savedHeapAtMethodPre, 
            services);
	final Term variant = inst.inv.getVariant(inst.selfTerm, 
						 heapAtMethodPre, 
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
	
	//prepare heapBeforeLoop, localOutBeforeLoop
	final LocationVariable heapBeforeLoop 
		= TB.heapAtPreVar(services, "heapBeforeLoop", true);
	services.getNamespaces().programVariables().addSafely(heapBeforeLoop);
	Term beforeLoopUpdate = TB.elementary(services, 
					      heapBeforeLoop, 
				              TB.heap(services));
    final Map<Term,Term> savedToBeforeLoop = new HashMap<Term,Term>();
	if(transaction) {
	    final LocationVariable savedHeapBeforeLoop
	        = TB.heapAtPreVar(services, "savedHeapBeforeLoop", true);
	    beforeLoopUpdate = TB.parallel(beforeLoopUpdate, TB.elementary(services, 
                savedHeapBeforeLoop, 
                    TB.savedHeap(services)));
	    savedToBeforeLoop.put(TB.savedHeap(services), TB.var(savedHeapBeforeLoop));
        savedToBeforeLoop.put(TB.heap(services), TB.var(savedHeapBeforeLoop));
	}
	final Map<Term,Term> normalToBeforeLoop = new HashMap<Term,Term>();
	normalToBeforeLoop.put(TB.heap(services), TB.var(heapBeforeLoop));
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
	    normalToBeforeLoop.put(TB.var(pv), TB.var(pvBeforeLoop));
	}
	
	//prepare anon update, frame condition
	final Pair<Term,Term> anonUpdateAndHeap 
		= createAnonUpdate(inst.loop, mod, localOuts, services);
	final Term anonUpdate;
	final Term anonHeapWellFormed;
	if(transaction) {
	    final Pair<Term,Term> anonUpdateAndHeapSaved  
	      = createAnonUpdate(inst.loop, modBackup, null, services);
	  anonUpdate = TB.parallel(anonUpdateAndHeap.first, anonUpdateAndHeapSaved.first);
	  anonHeapWellFormed   = TB.and(TB.wellFormed(services, anonUpdateAndHeap.second), TB.wellFormed(services, anonUpdateAndHeapSaved.second));
	}else{
	  anonUpdate = anonUpdateAndHeap.first;
	  anonHeapWellFormed   = TB.wellFormed(services, anonUpdateAndHeap.second);	    
	}

	// special case frame condition for strictly pure loops
	final Term normalFrameCondition;
	if(TB.lessThanNothing().equals(mod)) {
	    normalFrameCondition = TB.frameStrictlyEmpty(services, TB.heap(services), normalToBeforeLoop); 
	} else {
	    normalFrameCondition = TB.frame(services, TB.heap(services),
               normalToBeforeLoop, 
               mod);
	}
	final Term transactionFrameCondition = transaction ?
	          TB.frame(services, TB.savedHeap(services), savedToBeforeLoop, modBackup)
	        : null;

	final Term frameCondition = transactionFrameCondition != null ?
	        TB.and(normalFrameCondition,transactionFrameCondition) : normalFrameCondition;
	
	//prepare variant
	final ProgramElementName variantName 
		= new ProgramElementName(TB.newName(services, "variant"));
	final LocationVariable variantPV = new LocationVariable(variantName, 
								intKJT);
	services.getNamespaces().programVariables().addSafely(variantPV);
	final boolean dia = (inst.progPost.op() == Modality.DIA || inst.progPost.op() == Modality.DIA_TRANSACTION);
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
	final Term reachableState = TB.and(TB.wellFormedHeap(services), 
		                           reachableIn);
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
	bodyGoal.addFormula(new SequentFormula(anonHeapWellFormed), 
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
	if(props.getProperty(StrategyProperties.QUERY_OPTIONS_KEY)==StrategyProperties.QUERY_ON || 
	   props.getProperty(StrategyProperties.QUERY_OPTIONS_KEY)==StrategyProperties.QUERY_RESTRICTED){
	   invTerm2 = QueryExpand.INSTANCE.evaluateQueries(services, invTerm, true); //chrisg
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
	useGoal.addFormula(new SequentFormula(anonHeapWellFormed), 
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
