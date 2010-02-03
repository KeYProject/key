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

public class ListSort extends AbstractSort{

    public ListSort(Name name){
	super(name);
    }

    /**
     * @return the sorts of the successors of this sort
     */
    public SetOfSort extendsSorts(){
	return SetAsListOfSort.EMPTY_SET;
    }

}
