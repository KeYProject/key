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
import de.uka.ilkd.key.logic.Named;


public interface Sort extends Named {
    
    Sort FORMULA  = new PrimitiveSort(new Name("Formula"));
    Sort UPDATE   = new PrimitiveSort(new Name("Update"));
    Sort NULL     = new NullSortImpl(new Name("Null"));

    Sort ANY      = new AbstractSort(new Name("any")) {

            public SetOfSort extendsSorts() {            
                return SetAsListOfSort.EMPTY_SET;
            }
    
            public boolean extendsTrans(Sort s) {        
                return s == this;
            }
        
    };
    
    
    /**
     * Returns the direct supersorts of this sort.
     */
    SetOfSort extendsSorts();

    /**
     * Tells whether the given sort is a reflexive, transitive supersort of this 
     * sort.
     */
    boolean extendsTrans(Sort s);    
}
