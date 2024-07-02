// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.rule;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.rule.inst.SVInstantiations;


/** 
 * The variable condition adapter can be used by variable conditions
 * which can either fail or be successful, but which do not create a
 * constraint. 
 */
public abstract class VariableConditionAdapter implements VariableCondition {

    /**
     * checks if the condition for a correct instantiation is fulfilled
     * @param var the template Variable to be instantiated
     * @param instMap the MatchCondition with the current matching state and in particular 
     *    the SVInstantiations that are already known to be needed 
     * @param services the program information object
     * @return true iff condition is fulfilled
     */
    public abstract boolean check(SchemaVariable var, 
	    			  SVSubstitute instCandidate, 
				  SVInstantiations instMap, Services services);


    
    @Override
    public final MatchConditions check(SchemaVariable var, 
	    			       SVSubstitute instCandidate, 
	    			       MatchConditions mc, 
	    			       Services services) {
	return check(var, 
		     instCandidate, 
		     mc.getInstantiations(), 
		     services) 
	       ? mc 
	       : null;
    }
}