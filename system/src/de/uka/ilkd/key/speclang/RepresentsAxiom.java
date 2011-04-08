// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2011 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.speclang;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.ClassDeclaration;
import de.uka.ilkd.key.java.declaration.modifier.VisibilityModifier;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.OpReplacer;
import de.uka.ilkd.key.rule.RewriteTaclet;
import de.uka.ilkd.key.rule.RewriteTacletBuilder;
import de.uka.ilkd.key.rule.RewriteTacletGoalTemplate;
import de.uka.ilkd.key.rule.RuleSet;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.util.MiscTools;
import de.uka.ilkd.key.util.Pair;


/**
 * A class axiom corresponding to a JML* represents clause.
 */
public final class RepresentsAxiom implements ClassAxiom {
    
    private static final TermBuilder TB = TermBuilder.DF;
    
    private final String name;
    private final ObserverFunction target;
    private final KeYJavaType kjt;
    private final VisibilityModifier visibility;
    private final Term originalRep;
    private final ProgramVariable originalSelfVar;
    
    public RepresentsAxiom(String name,
	    		   ObserverFunction target, 
	                   KeYJavaType kjt,
	                   VisibilityModifier visibility,
	                   Term rep,
	                   ProgramVariable selfVar) {
	assert name != null;
	assert kjt != null;
	assert target != null;
	assert rep.sort() == Sort.FORMULA;
	assert (selfVar == null) == target.isStatic();
	this.name = name;
	this.target = target;
	this.kjt = kjt;
	this.visibility = visibility;
	this.originalRep = rep;
	this.originalSelfVar = selfVar;
    }
    
    
    private boolean isFunctional() {
	return originalRep.op() instanceof Equality
	       && originalRep.sub(0).op() == target
	       && (target.isStatic() 
		   || originalRep.sub(0).sub(1).op().equals(originalSelfVar));
    }
    
    
    private Term getAxiom(ParsableVariable heapVar, 
	    		  ParsableVariable selfVar,
	    		  Services services) {
	assert heapVar != null;
	assert (selfVar == null) == target.isStatic();
	final Map map = new HashMap();
	map.put(services.getTypeConverter().getHeapLDT().getHeap(), heapVar);	
	if(selfVar != null) {
	    map.put(originalSelfVar, selfVar);
	}
	final OpReplacer or = new OpReplacer(map);
	return or.replace(originalRep);
    }
    
    
    public static Pair<Term, ImmutableSet<Taclet>> limitTerm(
	    		Term t, 
	    		ImmutableSet<Pair<Sort, ObserverFunction>> toLimit, 
	    		Services services) {
	ImmutableSet<Taclet> taclets = DefaultImmutableSet.nil();
	
	//recurse to subterms
	Term[] subs = new Term[t.arity()];
	for(int i = 0; i < subs.length; i++) {
	     Pair<Term,ImmutableSet<Taclet>> pair 
	     	= limitTerm(t.sub(i), toLimit, services);
	     subs[i] = pair.first;
	     taclets = taclets.union(pair.second);
	}
	
	//top level operator
	Operator newOp = t.op();
	if(t.op() instanceof ObserverFunction) {
	    final ObserverFunction obs = (ObserverFunction) t.op();
	    for(Pair<Sort, ObserverFunction> pair : toLimit) {
		if(pair.second.equals(t.op())
	           && (obs.isStatic() 
	               || t.sub(1).sort().extendsTrans(pair.first))) {
		    Pair<ObserverFunction,ImmutableSet<Taclet>> limited
		    	= services.getSpecificationRepository().limitObs(obs); 
		    newOp = limited.first;
		    taclets = taclets.union(limited.second);
		}
	    }
	}
	
	//reassemble, return
	final Term term 
		= TB.tf().createTerm(newOp, subs, t.boundVars(), t.javaBlock());
	return new Pair<Term,ImmutableSet<Taclet>>(term, taclets);
    }    
    
    
    private static Pair<Term,ImmutableSet<VariableSV>> 
    				replaceBoundLVsWithSVsHelper(Term t) {
	ImmutableSet<VariableSV> svs = DefaultImmutableSet.<VariableSV>nil();
	
	//prepare op replacer, new bound vars
	final Map<Operator,Operator> map = new HashMap<Operator,Operator>();
	final ImmutableArray<QuantifiableVariable> boundVars 
		= t.boundVars();
	final QuantifiableVariable[] newBoundVars 
		= new QuantifiableVariable[boundVars.size()];	
	for(int i = 0; i < newBoundVars.length; i++) {
	    final QuantifiableVariable qv = boundVars.get(i);
	    if(qv instanceof LogicVariable) {
		final VariableSV sv 
			= SchemaVariableFactory.createVariableSV(qv.name(), 
							         qv.sort());
		svs = svs.add(sv);
		newBoundVars[i] = sv;
		map.put(qv, sv);
	    } else {
		newBoundVars[i] = qv;
	    }
	}
	final OpReplacer or = new OpReplacer(map);	
	
	//handle subterms
	final Term[] newSubs = new Term[t.arity()];
	boolean changedSub = false;
	for(int i = 0; i < newSubs.length; i++) {
	    if(t.op().bindVarsAt(i)) {
		newSubs[i] = or.replace(t.sub(i));
	    } else {
		newSubs[i] = t.sub(i);
	    }
	    final Pair<Term,ImmutableSet<VariableSV>> subPair 
	    	= replaceBoundLVsWithSVsHelper(newSubs[i]);
	    newSubs[i] = subPair.first;
	    svs = svs.union(subPair.second);
	    if(newSubs[i] != t.sub(i)) {
		changedSub = true;
	    }
	}
	
	//build overall term
	final Term newTerm;
	if(map.isEmpty() && !changedSub) {
	    newTerm = t;
	} else {
	    newTerm = TB.tf().createTerm(
		    	t.op(), 
		    	newSubs, 
		    	new ImmutableArray<QuantifiableVariable>(newBoundVars),
		        t.javaBlock());
	}
	
	return new Pair<Term,ImmutableSet<VariableSV>>(newTerm, svs);
    }
    
    
    /**
     * Replaces any bound logical variables in t with schema variables
     * (necessary for proof saving/loading, if t occurs as part of a taclet). 
     */
    public static Pair<Term,ImmutableSet<VariableSV>> 
    				replaceBoundLVsWithSVs(Term t) {
	//recursive replacement process
	final Pair<Term,ImmutableSet<VariableSV>> intermediateRes 
		= replaceBoundLVsWithSVsHelper(t);
	
	//Post-processing: different bound variables with the same name 
	//(but non-overlapping scopes) may be used in t; in contrast, the 
	//schema variables in this method's result must have names that are 
	//unique within the term.
	
	//collect all operator names used in t
	final OpCollector oc = new OpCollector();
	oc.visit(t);
	final Set<Name> usedNames = new HashSet<Name>();
	for(Operator op : oc.ops()) {
	    usedNames.add(op.name());
	}
	
	//find and resolve name conflicts between schema variables
	ImmutableSet<VariableSV> newSVs 
		= DefaultImmutableSet.<VariableSV>nil();
	final Set<Name> namesOfNewSVs = new HashSet<Name>();
	final Map<VariableSV,VariableSV> replaceMap 
		= new HashMap<VariableSV,VariableSV>(); 
	for(VariableSV sv : intermediateRes.second) {
	    if(namesOfNewSVs.contains(sv.name())) {
		//choose alternative name
		final String baseName = sv.name().toString();
		int i = 0;
		Name newName;
		do {
		    newName = new Name(baseName + "_" + i++);
		} while(usedNames.contains(newName));
		
		//create new SV, register in replace map
		final VariableSV newSV 
			= SchemaVariableFactory.createVariableSV(newName, 
								 sv.sort());
		newSVs = newSVs.add(newSV);
		namesOfNewSVs.add(sv.name());
		usedNames.add(sv.name());
		replaceMap.put(sv, newSV);
	    } else {
		newSVs = newSVs.add(sv);
		namesOfNewSVs.add(sv.name());
	    }
	}
	final OpReplacer or = new OpReplacer(replaceMap);
	final Term newTerm = or.replace(intermediateRes.first);	
	
	return new Pair<Term,ImmutableSet<VariableSV>>(newTerm, newSVs);
    }
    
    
    @Override
    public String getName() {
	return name;
    }
    
    
    @Override
    public ObserverFunction getTarget() {
	return target;
    }    
    

    @Override
    public KeYJavaType getKJT() {
	return kjt;
    }
    
    
    @Override
    public VisibilityModifier getVisibility() {
	return visibility;
    }

    
    public Taclet getRelationalTaclet(Services services) {
	final RewriteTacletBuilder tacletBuilder = new RewriteTacletBuilder();
	
	//create schema variables
	final HeapLDT heapLDT = services.getTypeConverter().getHeapLDT();
	final SchemaVariable heapSV 
		= SchemaVariableFactory.createTermSV(new Name("h"), 
						     heapLDT.targetSort(), 
						     false, 
						     false);
	final SchemaVariable selfSV
		= target.isStatic()
		  ? null
	          : SchemaVariableFactory.createTermSV(new Name("self"), 
						       kjt.getSort());
	
	//instantiate axiom with schema variables
	final Term rawAxiom = getAxiom(heapSV, selfSV, services);
	final Pair<Term,ImmutableSet<VariableSV>> replaceBoundLVsPair 
		= replaceBoundLVsWithSVs(rawAxiom);
	final Term schemaAxiom 
		= replaceBoundLVsPair.first;
	final ImmutableSet<VariableSV> boundSVs 
		= replaceBoundLVsPair.second;

	//prepare exactInstance guard
	final boolean finalClass 
		= kjt.getJavaType() instanceof ClassDeclaration 
	          && ((ClassDeclaration)kjt.getJavaType()).isFinal();
	final Term exactInstance 
		= target.isStatic() || finalClass
		  ? TB.tt() 
	          : TB.exactInstance(services, kjt.getSort(), TB.var(selfSV));
		  
        //prepare satisfiability guard
        final Term targetTerm 
        	= target.isStatic()
		  ? TB.func(target, TB.var(heapSV))
		  : TB.func(target, TB.var(heapSV), TB.var(selfSV));
        final Term axiomSatisfiable;
	if(target.sort() == Sort.FORMULA) {
	    axiomSatisfiable 
	    	= TB.or(OpReplacer.replace(targetTerm, TB.tt(), schemaAxiom),
		        OpReplacer.replace(targetTerm, TB.ff(), schemaAxiom));
	} else {
	    final VariableSV targetSV
	    	= SchemaVariableFactory.createVariableSV(
		    new Name(target.sort().name().toString().substring(0, 1) + "_lv"),
		    target.sort());
	    tacletBuilder.addVarsNotFreeIn(targetSV, heapSV);
	    if(!target.isStatic()) {
		tacletBuilder.addVarsNotFreeIn(targetSV, selfSV);
	    }	    
	    final Term targetLVReachable
	    	= TB.reachableValue(services, 
		    	      	    TB.var(heapSV), 
		    	      	    TB.var(targetSV), 
		    	      	    target.getType());
	    axiomSatisfiable = TB.ex(targetSV, 
		    		     TB.and(targetLVReachable,
		    			    OpReplacer.replace(targetTerm, 
			    		  	               TB.var(targetSV), 
			    		  	               schemaAxiom)));
	}
        	
	//assemble formula
	final Term guardedAxiom 
		= TB.imp(TB.and(exactInstance, axiomSatisfiable), schemaAxiom);
	final SequentFormula guardedAxiomCf 
		= new SequentFormula(guardedAxiom);
	
	//create taclet
	final Term findTerm = target.isStatic() 
	                      ? TB.func(target, TB.var(heapSV)) 
	                      : TB.func(target, TB.var(heapSV), TB.var(selfSV));
	tacletBuilder.setFind(findTerm);
	final Sequent addedSeq 
		= Sequent.createAnteSequent(
				Semisequent.EMPTY_SEMISEQUENT
		                           .insertFirst(guardedAxiomCf)
		                           .semisequent());	
	tacletBuilder.addTacletGoalTemplate
	    (new RewriteTacletGoalTemplate(addedSeq,
					   ImmutableSLList.<Taclet>nil(),
					   findTerm));
	tacletBuilder.setName(MiscTools.toValidTacletName(name));
	tacletBuilder.addRuleSet(
			new RuleSet(new Name("inReachableStateImplication")));
	for(VariableSV boundSV : boundSVs) {
	    tacletBuilder.addVarsNotFreeIn(boundSV, heapSV);
	    if(selfSV != null) {
		tacletBuilder.addVarsNotFreeIn(boundSV, selfSV);
	    }
	}
	
	return tacletBuilder.getTaclet();
    }
    
    
    @Override
    public ImmutableSet<Taclet> getTaclets(
	    		ImmutableSet<Pair<Sort, ObserverFunction>> toLimit,
	    		Services services) {
	//escape if axiom not functional
	if(!isFunctional()) {
	    return DefaultImmutableSet.<Taclet>nil()
	                              .add(getRelationalTaclet(services));
	}
	ImmutableSet<Taclet> result = DefaultImmutableSet.nil();
	
	//create schema variables
	final HeapLDT heapLDT = services.getTypeConverter().getHeapLDT();
	final SchemaVariable heapSV 
		= SchemaVariableFactory.createTermSV(new Name("h"), 
						     heapLDT.targetSort(), 
						     false, 
						     false);
	final SchemaVariable selfSV
		= target.isStatic()
		  ? null
	          : SchemaVariableFactory.createTermSV(originalSelfVar.name(), 
						       kjt.getSort());
	
	//instantiate axiom with schema variables
	final Term rawAxiom = getAxiom(heapSV, selfSV, services);
	final Pair<Term,ImmutableSet<VariableSV>> replaceBoundLVsPair 
		= replaceBoundLVsWithSVs(rawAxiom);
	final Term schemaAxiom 
		= replaceBoundLVsPair.first;
	final ImmutableSet<VariableSV> boundSVs 
		= replaceBoundLVsPair.second;	
	assert schemaAxiom.op() instanceof Equality;
	final Term schemaLhs = schemaAxiom.sub(0);
	final Term schemaRhs = schemaAxiom.sub(1);
	
	//limit observers
	final Pair<Term, ImmutableSet<Taclet>> limited 
		= limitTerm(schemaRhs, toLimit, services);
	final Term limitedRhs = limited.first;
	result = result.union(limited.second);
		
	//create if sequent
	final boolean finalClass 
		= kjt.getJavaType() instanceof ClassDeclaration 
		  && ((ClassDeclaration)kjt.getJavaType()).isFinal();
	final Sequent ifSeq;
	if(target.isStatic() || finalClass) {
	    ifSeq = null;
	} else {
	    final Term ifFormula 
	    	= TB.exactInstance(services, kjt.getSort(), TB.var(selfSV));
	    final SequentFormula ifCf = new SequentFormula(ifFormula);
	    final Semisequent ifSemiSeq 
	    	= Semisequent.EMPTY_SEMISEQUENT.insertFirst(ifCf).semisequent();
	    ifSeq = Sequent.createAnteSequent(ifSemiSeq);
	}
	
	//create taclet
	final RewriteTacletBuilder tacletBuilder = new RewriteTacletBuilder();
	tacletBuilder.setFind(schemaLhs);
	tacletBuilder.addTacletGoalTemplate
	    (new RewriteTacletGoalTemplate(Sequent.EMPTY_SEQUENT,
					   ImmutableSLList.<Taclet>nil(),
					   limitedRhs));
	if(ifSeq != null) {
	    tacletBuilder.setIfSequent(ifSeq);
	}
	tacletBuilder.setName(MiscTools.toValidTacletName(name));
	tacletBuilder.addRuleSet(new RuleSet(new Name("classAxiom")));
	for(VariableSV boundSV : boundSVs) {
	    tacletBuilder.addVarsNotFreeIn(boundSV, heapSV);
	    if(selfSV != null) {
		tacletBuilder.addVarsNotFreeIn(boundSV, selfSV);
	    }
	}	
	
	//add satisfiability branch
	final Term targetTerm 
		= target.isStatic()
		  ? TB.func(target, TB.var(heapSV))
	          : TB.func(target, TB.var(heapSV), TB.var(selfSV));
	final Term axiomSatisfiable;
	if(target.sort() == Sort.FORMULA) {
	    axiomSatisfiable 
	    	= TB.or(OpReplacer.replace(targetTerm, TB.tt(), schemaAxiom),
		        OpReplacer.replace(targetTerm, TB.ff(), schemaAxiom));
	} else {
	    final VariableSV targetSV
        	= SchemaVariableFactory.createVariableSV(
        		new Name(target.sort().name().toString().substring(0, 1)),
        		target.sort());
	    tacletBuilder.addVarsNotFreeIn(targetSV, heapSV);
	    if(!target.isStatic()) {
		tacletBuilder.addVarsNotFreeIn(targetSV, selfSV);
	    }
	    final Term targetSVReachable
	    	= TB.reachableValue(services, 
		    	      	    TB.var(heapSV), 
		    	      	    TB.var(targetSV), 
		    	      	    target.getType());	    
	    axiomSatisfiable = TB.ex(targetSV, 
                	             TB.and(targetSVReachable,
                	        	    OpReplacer.replace(targetTerm, 
                	        		   	       TB.var(targetSV), 
                	        		   	       schemaAxiom)));
        }
        SequentFormula addedCf = new SequentFormula(axiomSatisfiable);
	final Semisequent addedSemiSeq 
	    	= Semisequent.EMPTY_SEMISEQUENT.insertFirst(addedCf)
	    	                               .semisequent();
	final Sequent addedSeq = Sequent.createSuccSequent(addedSemiSeq);
	final SchemaVariable skolemSV 
		= SchemaVariableFactory.createSkolemTermSV(new Name("sk"), 
	        	  				   target.sort());
	tacletBuilder.addVarsNewDependingOn(skolemSV, heapSV);
	if(!target.isStatic()) {
	    tacletBuilder.addVarsNewDependingOn(skolemSV, selfSV);
	}
	tacletBuilder.addTacletGoalTemplate
	    (new RewriteTacletGoalTemplate(addedSeq,
					   ImmutableSLList.<Taclet>nil(),
					   TB.var(skolemSV)));
	tacletBuilder.goalTemplates().tail().head().setName("Use Axiom");
	tacletBuilder.goalTemplates().head().setName("Show Axiom Satisfiability");
	tacletBuilder.setStateRestriction(RewriteTaclet.SAME_UPDATE_LEVEL);
	result = result.add(tacletBuilder.getTaclet());
	
	//return
	return result;
    }
    
    
    @Override
    public ImmutableSet<Pair<Sort, ObserverFunction>> getUsedObservers(
	    						Services services) {
	if(!isFunctional()) {
	    return DefaultImmutableSet.nil();
	} else {
	    return MiscTools.collectObservers(originalRep.sub(1));
	}
    }    
    
    
    @Override
    public String toString() {
	return originalRep.toString();
    }


    @Override
    public String getDisplayName() {
	return getName();
    }
}
