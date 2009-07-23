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

public class PrimitiveSort extends AbstractSort {
    
    private static final SetOfSort EMPTY_SORT_SET 
    = SetAsListOfSort.EMPTY_SET;

    /** direct supersorts */
    private final SetOfSort ext;
       
    public PrimitiveSort(Name name, SetOfSort ext) {
        super(name);
        this.ext = ext;
    }
    
    /** creates a Sort (with a new equality symbol for this sort) */
    public PrimitiveSort(Name name) {
        this(name, EMPTY_SORT_SET);        
    }
    

    @Override    
    public SetOfSort extendsSorts () {
        return ext;
    }
    
    
    @Override
    public boolean isAbstract() {
	return false;
    }
}
