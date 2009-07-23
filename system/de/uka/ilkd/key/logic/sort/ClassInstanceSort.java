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

import de.uka.ilkd.key.logic.Name;

public class ClassInstanceSort extends AbstractSort {


    final SetOfSort ext;
    /** this field indicates if a <get> function shall be created or not */
    final boolean representsAbstractJavaOrInterfaceSort;
    
    
    /** creates a ClassInstanceSort*/
    public ClassInstanceSort(Name name, SetOfSort ext, boolean abs) {
	super(name);
	this.ext = ext;	
        this.representsAbstractJavaOrInterfaceSort = abs;
    }

    /** creates a ClassInstanceSort*/
    public ClassInstanceSort(Name name, de.uka.ilkd.key.logic.sort.Sort ext,
            boolean abs) {
	this(name, SetAsListOfSort.EMPTY_SET.add(ext), abs);
    }


    /** creates a ClassInstanceSort*/
    public ClassInstanceSort(Name name, boolean abs) {
	this(name, SetAsListOfSort.EMPTY_SET, abs);
    }

   
    /**
     * @return the sorts of the predecessors of this sort
     */
    public SetOfSort extendsSorts() {
        return ext;
    }

    public boolean representAbstractClassOrInterface() {        
        return representsAbstractJavaOrInterfaceSort;
    }   
    
    public boolean isAbstract() {
	return representsAbstractJavaOrInterfaceSort;
    }
}
