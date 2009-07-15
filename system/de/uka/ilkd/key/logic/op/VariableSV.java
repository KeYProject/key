// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.logic.op;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.util.Debug;

public final class VariableSV extends AbstractSV implements QuantifiableVariable {

    /** 
     * Creates a new SchemaVariable that is used as placeholder for
     * bound(quantified) variables.
     * @param name the Name of the SchemaVariable
     * @param sort the Sort of the SchemaVariable and the matched type     
     */
    VariableSV(Name name, Sort sort) {
	super(name, EMPTY_ARG_SORTS, sort, true, false); 	
    }

    
    @Override
    public MatchConditions match(SVSubstitute substitute, 
	    			 MatchConditions mc, 
	    			 Services services) {                
        final Term subst;
        if (substitute instanceof LogicVariable) {
            subst = TermFactory.DEFAULT.createVariableTerm((LogicVariable)substitute);
        } else if (substitute instanceof Term && 
                ((Term)substitute).op() instanceof QuantifiableVariable) {
            subst = (Term) substitute;
        } else {
            Debug.out("Strange Exit of match in VariableSV. Check for bug");
            return null;
        }
        final Term foundMapping = (Term)mc.getInstantiations ().
        	getInstantiation(this);
        if (foundMapping == null) {            		
            return addInstantiation(subst, mc, services);
        } else if (((QuantifiableVariable)foundMapping.op()) != subst.op()) {
            return null; //FAILED;			    
        } 
        return mc;
    } 
    
    
    @Override
    public String toString() {
	return toString("variable");
    }
}
