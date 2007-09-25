// This file is part of KeY - Integrated Deductive Software Design 
// Copyright (C) 2001-2003 Universitaet Karlsruhe, Germany
//                         and Chalmers University of Technology, Sweden          
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//

package de.uka.ilkd.asmkey.logic.sort;

import de.uka.ilkd.asmkey.unit.base.Int;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.op.Equality;
import de.uka.ilkd.key.logic.op.Op;
import de.uka.ilkd.key.logic.sort.CollectionSort;
import de.uka.ilkd.key.logic.sort.SetAsListOfSort;
import de.uka.ilkd.key.logic.sort.SetOfSort;
import de.uka.ilkd.key.logic.sort.Sort;

/**
 * This sort is needed to generate different collection sort than the standart
 * primitive sorts of key.
 *
 * @author Stanislas Nanchen
 */
public class PrimitiveSort extends de.uka.ilkd.key.logic.sort.PrimitiveSort {
    
    public static final PrimitiveSort INT = new PrimitiveSort(Int.builtInName());

    public static final PrimitiveSort ASMRULE = new SpecialSort(new Name("asm-rule"));

    /** special narity sort for the narity functions for big operators. */
    public static final SpecialSort nAritySort(Name func) {
	return new SpecialSort(new Name("narity-" + func));
    }

    private SequenceSort seqSort = new SequenceSort(this);
    private SetSort setSort = new SetSort(this);
    
    /** creates a Sort (with a new equality symbol for this sort) */
    public PrimitiveSort(Name name) {
	super(name);
    }
   
    public CollectionSort getSequenceSort() {
	return seqSort;
    }

    public CollectionSort getSetSort() {
	return setSort;
    }

    public static PrimitiveSort builtInSort(Name name) {
	if (INT.name().equals(name)) {
	    return INT;
	} else {
	    return null;
	}
    }

    private static class SpecialSort extends PrimitiveSort {
	
	public SpecialSort(Name name) { super (name);}

	public SetOfSort extendsSorts() {
	    return SetAsListOfSort.EMPTY_SET;
	}
	
	public boolean extendsTrans(Sort rhs) {
	    return SortUtil.extendsTrans(this, rhs);
	}
	
	public Equality getEqualitySymbol() {
	    return Op.EQUALS;
	}
	
	public String toString() {
	    return name.toString();
	}

    }

}
