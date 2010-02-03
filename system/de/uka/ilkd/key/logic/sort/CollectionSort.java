// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
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


public interface CollectionSort extends Sort {


    Sort elementSort();

    /**
     * @return the sorts of the predecessors of this sort
     */
    SetOfSort extendsSorts();

    /**
     * @return an object of this class with elementSort().equals(p),
     * or null if such an object cannot be constructed (as p is an
     * incompatible sort)
     */
    Sort cloneFor ( Sort p );

}
