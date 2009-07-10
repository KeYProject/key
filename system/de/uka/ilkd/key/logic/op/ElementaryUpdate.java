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

import java.util.WeakHashMap;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.sort.Sort;


public final class ElementaryUpdate extends AbstractSortedOperator {
    
    private static final WeakHashMap<UpdateableOperator, 
                                     ElementaryUpdate> instances 
    	= new WeakHashMap<UpdateableOperator, ElementaryUpdate>();
    
    
    private final UpdateableOperator lhs;

    
    private ElementaryUpdate(UpdateableOperator lhs) {
	super(new Name("elem-update(" + lhs + ")"), 
	      new Sort[]{lhs.sort()}, 
	      Sort.UPDATE);
	this.lhs = lhs;
	assert lhs.arity() == 0;
    }
    
    
    public static ElementaryUpdate getInstance(UpdateableOperator lhs) {
	ElementaryUpdate result = instances.get(lhs);
	if(result == null) {
	    result = new ElementaryUpdate(lhs);
	    instances.put(lhs, result);
	}
	return result;
    }


    @Override
    public boolean isRigid () {
	return true;
    }
    
    
    public Operator pv() {
	return lhs;
    }
}
