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

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.util.Debug;

/**
 * Schema variable that is instantiated with logical variables.
 */
public final class VariableSV extends AbstractSV implements QuantifiableVariable {

    /** 
     * Creates a new SchemaVariable that is used as placeholder for
     * bound(quantified) variables.
     * @param name the Name of the SchemaVariable
     * @param sort the Sort of the SchemaVariable and the matched type     
     */
    VariableSV(Name name, Sort sort) {
	super(name, sort, true, false); 	
    }

    
    @Override
    public MatchConditions match(SVSubstitute subst, 
	    			 MatchConditions mc, 
	    			 Services services) {                
        final Term substTerm;
        if(subst instanceof LogicVariable) {
            substTerm = services.getTermBuilder().var((LogicVariable)subst);
        } else if(subst instanceof Term && 
                 ((Term)subst).op() instanceof QuantifiableVariable) {
            substTerm = (Term) subst;
        } else {
            Debug.out("Strange Exit of match in VariableSV. Check for bug");
            return null;
        }
        final Term foundMapping 
        	= (Term)mc.getInstantiations().getInstantiation(this);
        if(foundMapping == null) {
            return addInstantiation(substTerm, mc, services);
        } else if (foundMapping.op() == substTerm.op()) {
            return mc;
        } else {
            Debug.out("FAILED. Already instantiated with different variable.");
            return null;	    
        }
    } 
    
    
    @Override
    public String toString() {
	return toString("variable");
    }
    
    
    @Override
    public String proofToString() {
	return "\\schemaVar \\variables " 
	       + sort().name() 
	       + " " 
	       + name() 
	       + ";\n";
    }    
}
