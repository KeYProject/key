// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.rule.conditions;

import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.SetLDT;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.rule.VariableConditionAdapter;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.util.InvInferenceTools;


public final class MetaDisjointCondition extends VariableConditionAdapter {
    
    private static final InvInferenceTools IIT = InvInferenceTools.INSTANCE;
    
    private final TermSV var1;
    private final TermSV var2;


    public MetaDisjointCondition(TermSV s1, TermSV s2) {
	this.var1 = s1;
	this.var2 = s2;
    }
    
    
    private static boolean clearlyDisjoint(Term t1, 
	    				   Term t2, 
	    				   Services services) {
	final SetLDT setLDT = services.getTypeConverter().getSetLDT();
	if(t1.op() instanceof Function && ((Function)t1.op()).isUnique()
           && t2.op() instanceof Function && ((Function)t2.op()).isUnique()
           && !t1.equals(t2)) {
	    return true;
	} else if(t1.sort().equals(setLDT.targetSort()) 
		  && t2.sort().equals(setLDT.targetSort())) {
	    final ImmutableSet<Term> t1set = IIT.unionToSet(t1, services);
	    final ImmutableSet<Term> t2set = IIT.unionToSet(t2, services);

	    ImmutableSet<Operator> t1Ops 
	    	= DefaultImmutableSet.<Operator>nil();
	    ImmutableSet<Operator> t2Ops 
	    	= DefaultImmutableSet.<Operator>nil();
	    for(Term t : t1set) {
		if(t.op().equals(setLDT.getSingleton())
		   && t.sub(0).op() instanceof Function 
		   && ((Function)t.sub(0).op()).isUnique()) {
		    t1Ops = t1Ops.add(t.op());
		} else if(t.op().equals(setLDT.getEmpty())){
		    continue;
		} else {
		    return false;
		}
	    }
	    for(Term t : t2set) {
		if(t.op().equals(setLDT.getSingleton())
		   && t.sub(0).op() instanceof Function 
		   && ((Function)t.sub(0).op()).isUnique()) {
		    t2Ops = t2Ops.add(t.op());
		} else if(t.op().equals(setLDT.getEmpty())){
		    continue;
		} else {
		    return false;
		}
	    }
	    
	    return t1Ops.intersect(t2Ops).isEmpty();	    
	} else {
	    return false;
	}
    }
    

    @Override
    public boolean check(SchemaVariable var, 
			 SVSubstitute subst, 
			 SVInstantiations svInst,
			 Services services) {
	final Term s1Inst = (Term) svInst.getInstantiation(var1);
	final Term s2Inst = (Term) svInst.getInstantiation(var2);
	if(s1Inst == null || s2Inst == null) {
	    return true;
	} else {
	    return clearlyDisjoint(s1Inst, s2Inst, services);
	}
    }

    
    @Override    
    public String toString () {
	return ("\\metaDisjoint " + var1 + ", " + var2);
    }
}
