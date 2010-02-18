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

import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.logic.Name;

public class ClassInstanceSortImpl extends AbstractNonCollectionSort 
    implements ClassInstanceSort {


    final ImmutableSet<Sort> ext;
    /** this field indicates if a <get> function shall be created or not */
    final boolean representsAbstractJavaOrInterfaceSort;
    
    
    /** creates a ClassInstanceSort*/
    public ClassInstanceSortImpl(Name name, ImmutableSet<Sort> ext, boolean abs) {
	super(name);
	this.ext = ext;	
        this.representsAbstractJavaOrInterfaceSort = abs;
    }

    /** creates a ClassInstanceSort*/
    public ClassInstanceSortImpl(Name name, de.uka.ilkd.key.logic.sort.Sort ext,
            boolean abs) {
	this(name, DefaultImmutableSet.<Sort>nil().add(ext), abs);
    }


    /** creates a ClassInstanceSort*/
    public ClassInstanceSortImpl(Name name, boolean abs) {
	this(name, DefaultImmutableSet.<Sort>nil(), abs);
    }

   
    /**
     * @return the sorts of the predecessors of this sort
     */
    public ImmutableSet<Sort> extendsSorts() {
        return ext;
    }

    public boolean representAbstractClassOrInterface() {        
        return representsAbstractJavaOrInterfaceSort;
    }   
}
