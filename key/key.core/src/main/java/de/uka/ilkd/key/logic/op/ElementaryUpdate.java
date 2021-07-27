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

package de.uka.ilkd.key.logic.op;

import java.lang.ref.WeakReference;
import java.util.WeakHashMap;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.sort.Sort;


/**
 * Class of operators for elementary updates, i.e., updates of the form 
 * "x := t". There is one such operator for every left hand side "x".
 * Each of these operator is unary, accepting a single argument "t".
 */
public final class ElementaryUpdate extends AbstractSortedOperator {
    
    private static final WeakHashMap<UpdateableOperator, 
                                     WeakReference<ElementaryUpdate>> instances 
    	= new WeakHashMap<UpdateableOperator, WeakReference<ElementaryUpdate>>();
    
    
    private final UpdateableOperator lhs;

    
    private ElementaryUpdate(UpdateableOperator lhs) {
	super(new Name("elem-update(" + lhs + ")"), 
	      new Sort[]{lhs.sort()}, 
	      Sort.UPDATE,
	      false);
	this.lhs = lhs;
	assert lhs.arity() == 0;
    }
    
    
    /**
     * Returns the elementary update operator for the passed left hand side.
     */
    public static ElementaryUpdate getInstance(UpdateableOperator lhs) {
	WeakReference<ElementaryUpdate> result = instances.get(lhs);
	if(result == null || result.get() == null) {
	    result = new WeakReference<ElementaryUpdate>(new ElementaryUpdate(lhs));
	    instances.put(lhs, result);
	}
	return result.get();
    }
    
    
    /**
     * Returns the left hand side of this elementary update operator.
     */
    public UpdateableOperator lhs() {
	return lhs;
    }
}