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


/** 
 * The instantiations of a schemavariable can be restricted on rule scope by 
 * attaching conditions on these variables. Such a condition is realized by a class 
 * which implements this interface. 
 * 
 * The usual place where to put these implementations is inside package
 * <code>de.uka.ilkd.key.rule.conditions</code>.  For variable conditions
 * that know only black and white answers there exists a convenience class 
 * {@link de.uka.ilkd.key.rule.VariableConditionAdapter}.     
 */
public interface VariableCondition {

    /**
     * checks if the condition for a correct instantiation is fulfilled
     * @param var the SchemaVariable to be instantiated
     * @param instCandidate the SVSubstitute (e.g. Term, ProgramElement) to be mapped to var
     * @param matchCond the MatchCondition with the current matching state and in particular 
     *    the SVInstantiations that are already known to be needed 
     * @param services the program information object
     * @return modified match results if the condition can be satisfied,
     * or <code>null</code> otherwise
     */
    MatchConditions check(SchemaVariable var, 
	    		  SVSubstitute instCandidate, 
	    		  MatchConditions matchCond, 
	    		  Services services);

}