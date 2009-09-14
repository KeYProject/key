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
import java.util.Map;

import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.OpReplacer;
import de.uka.ilkd.key.rule.RewriteTacletBuilder;
import de.uka.ilkd.key.rule.RewriteTacletGoalTemplate;
import de.uka.ilkd.key.rule.RuleSet;
import de.uka.ilkd.key.rule.Taclet;


public final class ClassAxiomImpl implements ClassAxiom {
    
    private static final TermBuilder TB = TermBuilder.DF;
    
    private final String name;
    private final KeYJavaType kjt;        
    private final ObserverFunction target;
    private final Term originalAxiom;
    private final ProgramVariable originalSelfVar;
    
    public ClassAxiomImpl(String name,
	                  KeYJavaType kjt, 	    
	    		  ObserverFunction target, 
	                  Term axiom,
	                  ProgramVariable selfVar) {
	assert name != null;
	assert kjt != null;
	assert target != null;
	assert axiom.sort() == Sort.FORMULA;
	assert (selfVar == null) == target.isStatic();
	this.name = name;
	this.target = target;
	this.kjt = kjt;
	this.originalAxiom = axiom;
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
	return or.replace(originalAxiom);
    }
    

    @Override
    public String getName() {
	return name;
    }
    

    @Override
    public KeYJavaType getKJT() {
	return kjt;
    }
    
    
    @Override
    public ObserverFunction getTarget() {
	return target;
    }

    
    @Override
    public Term getAxiom(Services services) {
	final HeapLDT heapLDT = services.getTypeConverter().getHeapLDT();
	final LogicVariable heapLV
	      = new LogicVariable(new Name("h"), heapLDT.targetSort());
	final LogicVariable selfLV
	      = target.isStatic()
	        ? null
	        : new LogicVariable(originalSelfVar.name(), 
	    			    originalSelfVar.sort());
	final Term varAxiom = getAxiom(heapLV, selfLV, services); 
	final Term varAxiom2 
		= target.isStatic() ? varAxiom : TB.all(selfLV, varAxiom); 
	return TB.all(heapLV, varAxiom2);
    }
    
    
    @Override
    public Taclet getAxiomAsTaclet(Services services) {
	if(!(originalAxiom.op() instanceof Equality)) {
	    return null;
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
	tacletBuilder.addRuleSet(new RuleSet(new Name("simplify")));
	
	return tacletBuilder.getTaclet();
    }    
    
    
    @Override
    public String toString() {
	return originalAxiom.toString();
    }
}
