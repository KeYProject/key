// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
// 


package de.uka.ilkd.key.logic.op;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.inst.IllegalInstantiationException;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.util.Debug;


/**
 * Abstract base class for schema variables.
 */
abstract class AbstractSV extends AbstractSortedOperator 
                          implements SchemaVariable {   
    
    private final boolean isStrict;
    
    
    protected AbstractSV(Name name, 
	                 ImmutableArray<Sort> argSorts, 
	                 Sort sort,
	                 boolean isRigid,
	                 boolean isStrict) {
	super(name, argSorts, sort, isRigid);
	this.isStrict = isStrict;
    }
    
    
    protected AbstractSV(Name name, 
	                 Sort[] argSorts, 
	                 Sort sort,
	                 boolean isRigid,
	                 boolean isStrict) {
	this(name, new ImmutableArray<Sort>(argSorts), sort, isRigid, isStrict);
    }
    
    
    protected AbstractSV(Name name,  
	                 Sort sort,
	                 boolean isRigid,
	                 boolean isStrict) {
	this(name,(ImmutableArray<Sort>) null, sort, isRigid, isStrict);
    }    
    
    
    /**
     * tries to add the pair <tt>(this,pe)</tt> to the match conditions. If
     * possible the resulting match conditions are returned, otherwise
     * <tt>null</tt>. Such an addition can fail, e.g. if already a pair
     * <tt>(this,x)</tt> exists where <tt>x<>pe</tt>
     */
    protected MatchConditions addInstantiation(ProgramElement pe,
	    				       MatchConditions matchCond, 
	    				       Services services) {

	final SVInstantiations instantiations = matchCond.getInstantiations();
	final SVSubstitute inMap = (SVSubstitute) instantiations
	.getInstantiation(this);

	if (inMap == null) {            
	    try {
		return matchCond
		.setInstantiations(instantiations.add(this, pe, services));
	    } catch (IllegalInstantiationException e) {
		Debug
		.out("Exception thrown by class Taclet at setInstantiations");
	    }
	} else {
	    Object peForCompare = pe;
	    if (inMap instanceof Term) {
		try {
		    peForCompare = services.getTypeConverter()
		    .convertToLogicElement(
			    pe,
			    matchCond.getInstantiations()
			    .getExecutionContext());                    
		} catch (RuntimeException re) {
		    Debug.out("Cannot convert program element to term.", this,
			    pe);
		    return null;
		}
	    } 
	    if (inMap.equals(peForCompare)) {
		return matchCond;
	    }
	}
	Debug.out("FAILED. Illegal Instantiation.", this, pe);
	return null;
    }
    
    
    /**
     * Tries to add the pair <tt>(this,term)</tt> to the match conditions. If
     * successful the resulting conditions are returned, otherwise null. Failure
     * is possible e.g. if this schemavariable has been already matched to a
     * term <tt>t2</tt> which is not unifiable with the given term.
     */
    protected final MatchConditions addInstantiation(Term term,
            					     MatchConditions matchCond, 
            					     Services services) {

        if (this.isRigid() && !term.isRigid()) {
            Debug.out("FAILED. Illegal Instantiation");
            return null;
        }      
        
        final SVInstantiations inst = matchCond.getInstantiations();

        final Term t = inst.getTermInstantiation(this, 
        		                         inst.getExecutionContext(), 
        				         services);
        if(t != null) {
            if(!t.equalsModRenaming(term)) {
        	Debug.out("FAILED. Adding instantiations leads to unsatisfiable"
        		+ " constraint.", 
        		this, 
        		term);
        	return null;
            } else {
        	return matchCond;
            }
        }

        try {           
            return matchCond.setInstantiations(inst.add(this, term, services));
        } catch (IllegalInstantiationException e) {
            Debug.out("FAILED. Exception thrown at sorted schema variable", e);
        }

        Debug.out("FAILED. Illegal Instantiation");
        return null;
    }
    
    
    protected final String toString(String sortSpec) {
	return name() +" (" + sortSpec + ")"; 
    }    

    
    @Override
    public final boolean isStrict() {
	return isStrict;
    }
    
    
    @Override
    public abstract MatchConditions match(SVSubstitute subst, 
	                  		  MatchConditions mc, 
	                  		  Services services);
}
