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
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
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
	this.name = name;
	this.target = target;
	this.kjt = kjt;
	this.originalAxiom = axiom;
	this.originalSelfVar = selfVar;
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
    public Term getAxiom(ProgramVariable selfVar, Services services) {
	Map map = new HashMap();
	map.put(originalSelfVar, selfVar);
	OpReplacer or = new OpReplacer(map);
	return or.replace(originalAxiom);
    }
    
    
    @Override
    public Taclet getAxiomAsTaclet(ProgramVariable selfVar, Services services) {
	final Term axiomTerm = getAxiom(selfVar, services);
	if(!(axiomTerm.op() instanceof Equality)) {
	    return null;
	}
	final Term lhs = axiomTerm.sub(0);
	final Term rhs = axiomTerm.sub(1);
	
	final HeapLDT heapLDT = services.getTypeConverter().getHeapLDT();
	final SchemaVariable heapSV 
		= SchemaVariableFactory.createTermSV(new Name("h"), 
						     heapLDT.targetSort(), 
						     false, 
						     false);
	final Map map = new HashMap();
	map.put(TB.heap(services), TB.var(heapSV));
	final OpReplacer or = new OpReplacer(map);
	final Term schemaLhs = or.replace(lhs);
	final Term schemaRhs = or.replace(rhs);
	
	RewriteTacletBuilder tacletBuilder = new RewriteTacletBuilder();
	tacletBuilder.setFind(schemaLhs);
	tacletBuilder.addTacletGoalTemplate
	    (new RewriteTacletGoalTemplate(Sequent.EMPTY_SEQUENT,
					   ImmutableSLList.<Taclet>nil(),
					   schemaRhs));
	tacletBuilder.setName(new Name(name));
	tacletBuilder.addRuleSet(new RuleSet(new Name("simplify")));
	
	return tacletBuilder.getTaclet();
    }    
    
    
    @Override
    public String toString() {
	return originalAxiom.toString();
    }
}
