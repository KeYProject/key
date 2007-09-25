// This file is part of KeY - Integrated Deductive Software Design 
// Copyright (C) 2001-2003 Universitaet Karlsruhe, Germany
//                         and Chalmers University of Technology, Sweden          
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//

package de.uka.ilkd.asmkey.logic.sort;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.sort.CollectionSort;

/**
 * This sort is needed to generate different collection sorts than the standart
 * generic sorts of key.
 *
 * furthermore, because of derived terms and functions, we need to "instanciate"
 * the generic sort with concrete sort already during the parsing of terms, if
 * necessary.
 *
 * @author Stanislas Nanchen
 */
public class GenericSort extends de.uka.ilkd.key.logic.sort.GenericSort {

    private SequenceSort seqSort = new SequenceSort(this);
    private SetSort setSort = new SetSort(this);
    
    /** creates a Sort (with a new equality symbol for this sort) */
    public GenericSort(Name name) {
	super(name);
    }
   
    public CollectionSort getSequenceSort() {
	return seqSort;
    }

    public CollectionSort getSetSort() {
	return setSort;
    }

    public boolean extendsTrans(de.uka.ilkd.key.logic.sort.Sort sort) {
	return true;
    }
    
}
