// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
//
//

package de.uka.ilkd.key.logic.sort;

import de.uka.ilkd.key.logic.Name;


public abstract class AbstractCollectionSort 
    extends AbstractSort implements CollectionSort {

    final Sort elementSort;

    
    /** creates a Sort (with a new equality symbol for this sort) */
    public AbstractCollectionSort(String name, Sort elemSort) {
        super(new Name(name));
        elementSort=elemSort;
    }

    public Sort elementSort() {
        return elementSort;
    }
   

    /**
     * @return an object of this class with elementSort().equals(p),
     * or null if such an object cannot be constructed (as p is an
     * incompatible sort)
     */
    public Sort cloneFor ( Sort p ) {
        throw new RuntimeException ( "Method has not been written" );
    }


    /**
     * @return the sorts of the predecessors of this sort
     */
    public SetOfSort extendsSorts() {
	return SetAsListOfSort.EMPTY_SET;
    }
}
