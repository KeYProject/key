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

public final class SortImpl extends AbstractSort {
    
    public SortImpl(Name name, SetOfSort ext, boolean isAbstract) {
        super(name, ext, isAbstract);
    }    
    
    public SortImpl(Name name, SetOfSort ext) {
        this(name, ext, false);
    }
    
    public SortImpl(Name name, Sort ext) {
        this(name, SetAsListOfSort.EMPTY_SET.add(ext), false);
    }    
    

    public SortImpl(Name name) {
        this(name, SetAsListOfSort.EMPTY_SET);        
    }
}
