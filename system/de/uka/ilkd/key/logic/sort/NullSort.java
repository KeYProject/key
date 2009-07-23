// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.logic.sort;

import de.uka.ilkd.key.logic.Name;


public class NullSort extends ClassInstanceSort  {

    public NullSort(Name name) {
	super(name, false);
    }
    
    
    @Override
    public SetOfSort extendsSorts() {
	assert false : "not supported by NullSort";
    	return null;
    }
    

    @Override
    public boolean extendsTrans(Sort s) {
	if(s == this || s == Sort.ANY) {
	    return true;
	}
	SetOfSort sups = SetAsListOfSort.EMPTY_SET.add(s);
	while(!sups.isEmpty()) {
	    final SetOfSort oldSups = sups;
	    sups = SetAsListOfSort.EMPTY_SET;
	    for(Sort sup : oldSups) {
		if(sup.name().toString().equals("java.lang.Object")
			|| sup.name().toString().equals("Object")) { //HACK
		    return true;
		} else {
		    sups = sups.union(sup.extendsSorts());
		}
	    }
	}
	
       return false;
    }
}