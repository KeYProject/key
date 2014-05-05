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

package de.uka.ilkd.key.logic.sort;

import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.logic.Name;

/**
 * Standard implementation of the Sort interface.
 */
public final class SortImpl extends AbstractSort {
    
    public SortImpl(Name name, ImmutableSet<Sort> ext, boolean isAbstract) {
        super(name, ext, isAbstract);
    }    
    
    public SortImpl(Name name, ImmutableSet<Sort> ext) {
        this(name, ext, false);
    }
    
    public SortImpl(Name name, Sort ext) {
        this(name, DefaultImmutableSet.<Sort>nil().add(ext), false);
    }    
    

    public SortImpl(Name name) {
        this(name, DefaultImmutableSet.<Sort>nil());        
    }
    
    public boolean equals(Object o){
        if (o instanceof SortImpl){
            return ((SortImpl)o).name().equals(name());
        } else return false;
    }

}