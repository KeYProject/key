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

import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.modifier.VisibilityModifier;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.proof.OpReplacer;
import de.uka.ilkd.key.rule.AntecTacletBuilder;
import de.uka.ilkd.key.rule.RuleSet;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.TacletGoalTemplate;


public final class PartialInvAxiom implements ClassAxiom {
    
    private static final TermBuilder TB = TermBuilder.DF;
    
    private final ClassInvariant inv;
    private final ObserverFunction target;
    
    public PartialInvAxiom(ClassInvariant inv, Services services) {
	assert inv != null;
	this.inv = inv;
	this.target = services.getJavaInfo().getInv();
	assert target != null;
    }
    
    
    @Override
    public String getName() {
	return inv.getName();
    }

    
    @Override
    public ObserverFunction getTarget() {
	return target;
    }
    

    @Override
    public KeYJavaType getKJT() {
	return inv.getKJT();
    }
    
    
    @Override
    public VisibilityModifier getVisibility() {
	return inv.getVisibility();
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
	        : new LogicVariable(new Name("self"), 
	    			    inv.getKJT().getSort());
	final Term varAxiom 
		= OpReplacer.replace(TB.heap(services), 
				     TB.var(heapLV), 
				     inv.getInv(selfLV, services));
        	
	//assemble formula
	final Term guardedAxiom 
		= TB.imp(TB.inv(services, TB.var(heapLV), TB.var(selfLV)), 
			 varAxiom); 
	final Term quantifiedAxiom 
		= target.isStatic() 
		  ? guardedAxiom 
	          : TB.all(selfLV, guardedAxiom);
	return TB.all(heapLV, quantifiedAxiom);
    }
    
    
    @Override
    public Taclet getAxiomAsTaclet(Services services) {
	//instantiate axiom with schema variables
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
						       inv.getKJT().getSort());
	final Term schemaAxiom 
		= OpReplacer.replace(TB.heap(services), 
				     TB.var(heapSV), 
				     inv.getInv(selfSV, services));
	
	//create added sequent
	final ConstrainedFormula addedCf = new ConstrainedFormula(schemaAxiom);	    
	final Semisequent addedSemiSeq 
	    	= Semisequent.EMPTY_SEMISEQUENT.insertFirst(addedCf)
	    	                               .semisequent();
	final Sequent addedSeq = Sequent.createAnteSequent(addedSemiSeq);	

	//create taclet
	final AntecTacletBuilder tacletBuilder = new AntecTacletBuilder();
	tacletBuilder.setFind(TB.inv(services, TB.var(heapSV), TB.var(selfSV)));
	tacletBuilder.addTacletGoalTemplate(
			new TacletGoalTemplate(addedSeq,
					       ImmutableSLList.<Taclet>nil()));
	tacletBuilder.setName(new Name("Partial inv axiom for " + inv.getName()));
	tacletBuilder.addRuleSet(new RuleSet(new Name("inReachableStateImplication")));
	
	//return
	return tacletBuilder.getTaclet();
    }
    
    
    @Override
    public String toString() {
	return inv.toString();
    }
}
