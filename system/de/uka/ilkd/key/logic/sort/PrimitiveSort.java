// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.logic.sort;

import de.uka.ilkd.key.logic.Name;

public class PrimitiveSort extends AbstractNonCollectionSort {
    
    private static final SetOfSort EMPTY_SORT_SET 
    = SetAsListOfSort.EMPTY_SET;

    /** direct supersorts */
    SetOfSort ext = EMPTY_SORT_SET;
    
    /** creates a Sort (with a new equality symbol for this sort) */
    public PrimitiveSort(Name name) {
        super(name);        
    }
    
    public PrimitiveSort(Name name, SetOfSort ext) {
        super( name );
        this.ext = ext;        
    }
   
    public SetOfSort extendsSorts () {
        return ext;
    }
    
    /**
     * @return the sorts of the predecessors of this sort
     */
    public boolean extendsTrans(Sort sort) {
        if (sort == this || sort == Sort.ANY) {
            return true;
        }
        
        if (!(sort instanceof PrimitiveSort)) {
            return false;
        }
                             
        final IteratorOfSort it = extendsSorts().iterator();
        while (it.hasNext()) {
            final Sort s = it.next();
            assert s!=null;
            if (s == sort || s.extendsTrans(sort)) {
                return true;
            }
        }
        return false;
    }
}
