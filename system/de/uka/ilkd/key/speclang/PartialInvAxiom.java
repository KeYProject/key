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
import de.uka.ilkd.key.rule.AntecTacletBuilder;
import de.uka.ilkd.key.rule.RuleSet;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.TacletGoalTemplate;
import de.uka.ilkd.key.util.MiscTools;
import de.uka.ilkd.key.util.Pair;


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
    public ImmutableSet<Taclet> getTaclets(
	    		ImmutableSet<Pair<Sort, ObserverFunction>> toLimit,
	    		Services services) {
	ImmutableSet<Taclet> result = DefaultImmutableSet.<Taclet>nil();
	
	for(int i = 0; i < 2; i++) {
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
	    final SchemaVariable eqSV 
	    	= target.isStatic()
	    	  ? null
		  : SchemaVariableFactory.createTermSV(
			  		new Name("EQ"), 
			    		services.getJavaInfo().objectSort());	    
	    final Term schemaAxiom 
	    	= OpReplacer.replace(TB.heap(services), 
	    			     TB.var(heapSV), 
	    			     inv.getInv(selfSV, services));
	    
	    //limit observers
	    final Pair<Term, ImmutableSet<Taclet>> limited 
	    	= RepresentsAxiom.limitTerm(schemaAxiom, toLimit, services);
	    final Term limitedAxiom = limited.first;
	    result = result.union(limited.second);
	    
	    //create added sequent
	    final ConstrainedFormula addedCf = new ConstrainedFormula(limitedAxiom);	    
	    final Semisequent addedSemiSeq 
	    	= Semisequent.EMPTY_SEMISEQUENT.insertFirst(addedCf) 
	    	                               .semisequent();
	    final Sequent addedSeq = Sequent.createAnteSequent(addedSemiSeq);	

	    //create taclet
	    final AntecTacletBuilder tacletBuilder = new AntecTacletBuilder();
	    tacletBuilder.setFind(TB.inv(services, 
		    		  TB.var(heapSV), 
		    		  i == 0 ? TB.var(selfSV) : TB.var(eqSV)));
	    tacletBuilder.addTacletGoalTemplate(
		    new TacletGoalTemplate(addedSeq,
			    ImmutableSLList.<Taclet>nil()));
	    tacletBuilder.setName(new Name("Partial inv axiom for " 
		    			   + inv.getName()
		    			   + (i == 0 ? "" : " EQ")));
	    tacletBuilder.addRuleSet(
		    	new RuleSet(new Name("inReachableStateImplication")));
	    
	    //\assumes(self = EQ ==>)
	    if(i == 1) {
		assert !target.isStatic();
		final Term ifFormula = TB.equals(TB.var(selfSV), TB.var(eqSV));
		final ConstrainedFormula ifCf 
			= new ConstrainedFormula(ifFormula);
		final Semisequent ifSemiSeq 
		    	= Semisequent.EMPTY_SEMISEQUENT.insertFirst(ifCf)
		                                       .semisequent();
		final Sequent ifSeq = Sequent.createAnteSequent(ifSemiSeq);
		tacletBuilder.setIfSequent(ifSeq);
	    }
	    
	    result = result.add(tacletBuilder.getTaclet());
	    
	    //EQ taclet only for non-static invariants
	    if(target.isStatic()) {
		break;
	    }
	}
	
	//return
	return result;
    }
    
    
    @Override
    public ImmutableSet<Pair<Sort, ObserverFunction>> getUsedObservers(
	    						Services services) {
	final ProgramVariable dummySelfVar 
		= TB.selfVar(services, inv.getKJT(), false);
	return MiscTools.collectObservers(inv.getInv(dummySelfVar, services));
    }
    
    
    @Override
    public String toString() {
	return inv.toString();
    }
}
