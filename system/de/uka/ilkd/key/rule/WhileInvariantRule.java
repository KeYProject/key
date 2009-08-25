// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.rule;

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
import de.uka.ilkd.key.util.InvInferenceTools;


public final class WhileInvariantRule implements BuiltInRule {

    public static final WhileInvariantRule INSTANCE = new WhileInvariantRule();

    private static final Name NAME = new Name("whileInvariant");
    private static final TermBuilder TB = TermBuilder.DF;
    private static final InvInferenceTools IIT = InvInferenceTools.INSTANCE;

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
	if(progPost.op() != Modality.BOX && progPost.op() != Modality.DIA) {
	    return null;
	}

	//active statement must be while loop
	SourceElement activeStatement 
		= IIT.getActiveStatement(progPost.javaBlock());
	if(!(activeStatement instanceof While)) {
	    return null;
	}
	final While loop = (While) activeStatement;

	//an invariant must be present for the loop
	final LoopInvariant inv 
		= services.getSpecificationRepository().getLoopInvariant(loop);
	if(inv == null 
           || inv.getInvariant(inv.getInternalSelfTerm(), 
        	   	       inv.getInternalHeapAtPre(), 
			       services) == null
	   || (progPost.op() == Modality.DIA 
	       && inv.getVariant(inv.getInternalSelfTerm(), 
		       		 inv.getInternalHeapAtPre(), 
		       		 services) == null)) {
	    return null;
	}

	//collect self, execution context
	final MethodFrame innermostMethodFrame 
		= IIT.getInnermostMethodFrame(progPost, services);
	final Term selfTerm = innermostMethodFrame == null
	                      ? null
	                      : IIT.getSelfTerm(innermostMethodFrame, services);
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

    
    private Term createAnonUpdate(While loop, Term mod, Services services) {
	//heap
	HeapLDT heapLDT = services.getTypeConverter().getHeapLDT();
	Name anonHeapName = new Name(TB.newName(services, "loopAnonHeap"));
	Function anonHeapFunc = new Function(anonHeapName,
					     heapLDT.targetSort());
	services.getNamespaces().functions().addSafely(anonHeapFunc);
	Term result = TB.elementary(services,
		                    heapLDT.getHeap(), 
		                    TB.changeHeapAtLocs(services, 
		                	    		TB.heap(services), 
		                	    		mod,
		                	    		TB.func(anonHeapFunc)));
	
	//local vars
	ImmutableSet<ProgramVariable> localVars 
		= IIT.getWrittenPVs(loop, services);
	for(ProgramVariable pv : localVars) {
	    String anonFuncName = TB.newName(services, pv.name().toString());
	    Function anonFunc = new Function(new Name(anonFuncName), pv.sort());
	    services.getNamespaces().functions().addSafely(anonFunc);
	    Term elemUpd = TB.elementary(services, 
		                         (LocationVariable)pv, 
		                         TB.func(anonFunc));
	    result = TB.parallel(result, elemUpd);
	}
	
	return result;
    }
    
    
    
    //-------------------------------------------------------------------------
    //public interface
    //-------------------------------------------------------------------------

    @Override
    public boolean isApplicable(Goal goal, 
	    			PosInOccurrence pio,
	    			Constraint userConstraint) {
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
	final Term heapAtMethodPre = inst.inv.getInternalHeapAtPre();
	final Term invTerm         = inst.inv.getInvariant(inst.selfTerm, 
		 	                                   heapAtMethodPre, 
		 	                                   services);
	final Term mod = inst.inv.getModifies(inst.selfTerm, 
					      heapAtMethodPre, 
					      services);
	final Term variant = inst.inv.getVariant(inst.selfTerm, 
						 heapAtMethodPre, 
						 services);
	
	//prepare heapBeforeLoop
	final LocationVariable heapBeforeLoop 
		= TB.heapAtPreVar(services, "heapBeforeLoop", true);
	services.getNamespaces().programVariables().addSafely(heapBeforeLoop);
	final Term heapBeforeLoopUpdate = TB.elementary(services, 
						        heapBeforeLoop, 
						        TB.heap(services));
	
	//prepare anon update, frame condition
	final Term anon = createAnonUpdate(inst.loop, mod, services);
	final Term frameCondition = TB.frame(services,
		                             TB.var(heapBeforeLoop), 
		                             mod);
	
	//prepare variant
	final ProgramElementName variantName 
		= new ProgramElementName(TB.newName(services, "variant"));
	final LocationVariable variantPV = new LocationVariable(variantName, 
								intKJT);
	services.getNamespaces().programVariables().add(variantPV);
	final boolean dia = inst.progPost.op() == Modality.DIA;
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
		= new Term[]{inst.u, anon};
	final Term[] uBeforeLoopDefAnonVariant 
		= new Term[]{inst.u, heapBeforeLoopUpdate, anon, variantUpdate};
	final Term uAnonInv 
		= TB.applySequential(uAnon, 
				     TB.and(invTerm, 
					    TB.wellFormedHeap(services)));
	final Term uAnonInvVariantNonNeg
		= TB.applySequential(uAnon, 
				     TB.and(TB.and(invTerm, 
					           TB.wellFormedHeap(services)),
					    variantNonNeg));

	//"Invariant Initially Valid":
	// \replacewith (==> inv );
	initGoal.changeFormula(new ConstrainedFormula(TB.apply(inst.u, invTerm)),
			       ruleApp.posInOccurrence());

	//"Body Preserves Invariant":
        // \replacewith (==>  #atPreEqs(anon1) 
 	//                       -> #introNewAnonUpdate(#modifies, #locDepFunc(anon1, \[{.. while (#e) #s ...}\]post) & inv -> 
        //                         (\[{ method-frame(#ex):{#typeof(#e) #v1 = #e;} }\]#v1=TRUE ->
        //                          #whileInvRule(\[{.. while (#e) #s ...}\]post, 
        //                               #locDepFunc(anon1, \[{.. while (#e) #s ...}\]post) & inv)),anon1));
	bodyGoal.addFormula(new ConstrainedFormula(uAnonInvVariantNonNeg), 
			    true, 
			    false);

	final WhileInvRule wir 
		= (WhileInvRule) AbstractMetaOperator.WHILE_INV_RULE;
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
	    System.out.println("AHA: " + sv);
	}
	Term bodyTerm = TB.tf().createTerm(wir, 
					   inst.progPost,
					   TB.and(invTerm, 
						  TB.and(frameCondition,
							 variantPO)));
	bodyTerm = wir.calculate(bodyTerm, svInst, services);
	final Term guardTrueBody = TB.box(guardJb, 
					  TB.imp(guardTrueTerm, bodyTerm)); 

	bodyGoal.changeFormula(new ConstrainedFormula(TB.applySequential(
						uBeforeLoopDefAnonVariant, 
						guardTrueBody)), 
                               ruleApp.posInOccurrence());

	// "Use Case":
	// \replacewith (==> #introNewAnonUpdate(#modifies, inv ->
	// (\[{ method-frame(#ex):{#typeof(#e) #v1 = #e;} }\]
	// (#v1=FALSE -> \[{.. ...}\]post)),anon2))
	useGoal.addFormula(new ConstrainedFormula(uAnonInv), true, false);

	Term restPsi = TB.prog(dia ? Modality.DIA : Modality.BOX,
		              IIT.removeActiveStatement(inst.progPost.javaBlock(), 
							services), 
                              inst.progPost.sub(0));
	Term guardFalseRestPsi = TB.box(guardJb, 
					TB.imp(guardFalseTerm, restPsi));
	useGoal.changeFormula(new ConstrainedFormula(TB.applySequential(
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
