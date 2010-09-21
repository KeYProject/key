// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
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
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
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
    
    
    private void collectObserversForSort(
	    			Term t, 
	    			Sort receiverSort,
	    			/*@out@*/Set<ObserverFunction> result) {
	if(t.op() instanceof ObserverFunction) {
	    ObserverFunction obs = (ObserverFunction)t.op();
	    if(obs.isStatic() 
	       && obs.getContainerType().getSort().equals(receiverSort)) {
		result.add(obs);
	    } else if(!obs.isStatic() && t.sub(1).sort().equals(receiverSort)) {
		result.add(obs);
	    }
	}
	for(Term sub : t.subs()) {
	    collectObserversForSort(sub, receiverSort, result);
	}
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

    
    @Override
    public Term getAxiom(Services services) {
	//instantiate axiom with logical variables
	final HeapLDT heapLDT = services.getTypeConverter().getHeapLDT();
	final LogicVariable heapLV
	      = new LogicVariable(new Name("h"), heapLDT.targetSort());
	final LogicVariable selfLV
	      = target.isStatic()
	        ? null
	        : new LogicVariable(originalSelfVar.name(), 
	    			    originalSelfVar.sort());
	final Term varAxiom = getAxiom(heapLV, selfLV, services);
	
	//prepare exactInstance guard
	final Term exactInstance 
		= target.isStatic() 
		  ? TB.tt() 
	          : TB.exactInstance(services, kjt.getSort(), TB.var(selfLV));
		  
        //prepare satisfiability guard
        final Term targetTerm 
        	= target.isStatic()
		  ? TB.func(target, TB.var(heapLV))
		  : TB.func(target, TB.var(heapLV), TB.var(selfLV));
        final Term axiomSatisfiable;
	if(target.sort() == Sort.FORMULA) {
	    axiomSatisfiable 
	    	= TB.or(OpReplacer.replace(targetTerm, TB.tt(), varAxiom),
		        OpReplacer.replace(targetTerm, TB.ff(), varAxiom));
	} else {
	    final LogicVariable targetLV
	    	= new LogicVariable(
		    new Name(target.sort().name().toString().substring(0, 1)),
		    target.sort());
	    final Term targetLVReachable
	    	= TB.reachableValue(services, 
		    	      	    TB.var(heapLV), 
		    	      	    TB.var(targetLV), 
		    	      	    target.getType());
	    axiomSatisfiable = TB.ex(targetLV, 
		    		     TB.and(targetLVReachable,
		    			    OpReplacer.replace(targetTerm, 
			    		  	               TB.var(targetLV), 
			    		  	               varAxiom)));
	}
        	
	//assemble formula
	final Term guardedAxiom 
		= TB.imp(TB.and(exactInstance, axiomSatisfiable), varAxiom); 
	final Term quantifiedAxiom 
		= target.isStatic() 
		  ? guardedAxiom 
	          : TB.all(selfLV, guardedAxiom);
	return TB.all(heapLV, quantifiedAxiom);
    }
    
    
    @Override
    public ImmutableSet<Taclet> getAxiomAsTaclet(Services services) {
	//abort if axiom not equational
	if(!(originalRep.op() instanceof Equality
	     && originalRep.sub(0).op() == target
	     && (target.isStatic() 
		 || originalRep.sub(0).sub(1).op().equals(originalSelfVar)))) {
	    return null;
	}
	
	//abort if axiom is obviously recursive (TODO: catch mutual recursion)
	final Set<ObserverFunction> usedObservers 
		= new HashSet<ObserverFunction>();
	collectObserversForSort(originalRep.sub(1), 
			        target.isStatic() 
			          ? target.getContainerType().getSort() 
			          : originalSelfVar.sort(), 
			        usedObservers);
	if(usedObservers.contains(target)) {
	    //return null;
	}

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
	final Term schemaAxiom = getAxiom(heapSV, selfSV, services);
	assert schemaAxiom.op() instanceof Equality;
	final Term schemaLhs = schemaAxiom.sub(0);
	final Term schemaRhs = schemaAxiom.sub(1);
	
	//create if sequent
	final Sequent ifSeq;
	if(target.isStatic()) {
	    ifSeq = null;
	} else {
	    final Term ifFormula 
	    	= TB.exactInstance(services, kjt.getSort(), TB.var(selfSV));
	    final ConstrainedFormula ifCf = new ConstrainedFormula(ifFormula);
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
					   schemaRhs));
	if(!target.isStatic()) {
	    tacletBuilder.setIfSequent(ifSeq);
	}
	tacletBuilder.setName(new Name(name));
	tacletBuilder.addRuleSet(new RuleSet(new Name("classAxiom")));
	
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
        ConstrainedFormula addedCf = new ConstrainedFormula(axiomSatisfiable);
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
	
	//return
	return DefaultImmutableSet.<Taclet>nil().add(tacletBuilder.getTaclet());
    }    
    
    
    @Override
    public String toString() {
	return originalRep.toString();
    }
}
