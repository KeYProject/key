// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//


package de.uka.ilkd.key.logic.sort.oclsort;

import java.util.Iterator;

import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.op.Equality;
import de.uka.ilkd.key.logic.op.Op;
import de.uka.ilkd.key.logic.sort.GenericSort;
import de.uka.ilkd.key.logic.sort.Sort;

public class CollectionSort implements OclSort {

    public static final int COLLECTION = 0;
    public static final int SET = 1;
    public static final int BAG = 2;
    public static final int SEQUENCE = 3;
    
    private int collectionKind;
    private OclSort elemSort;
    private Name name;
    private int hashcode = 0;

    public CollectionSort(int collectionKind, OclSort elemSort) {
	this.collectionKind = collectionKind;
	this.elemSort = elemSort;

	switch (this.collectionKind) {
	case COLLECTION:
	    name = new Name("OclCollectionOf" + elemSort.name());
	    break;
	case SET:
	    name = new Name("OclSetOf" + elemSort.name());
	    break;
	case BAG:
	    name = new Name("OclBagOf" + elemSort.name());
	    break;
	case SEQUENCE:
	    name = new Name("OclSequenceOf" + elemSort.name());
	    break;
	}
    }

    /** @return name of the Sort */
    public Name name() {
	return name;
    }

    public int getCollectionKind() {
	return collectionKind;
    }

    public OclSort getElemSort() {
	return elemSort;
    }

    public static CollectionSort getCollectionSort(int collectionKind,
						   OclSort elemSort) {
	switch(collectionKind) {
	case SET:
	    return getSetSort(elemSort);
	case BAG:
	    return getBagSort(elemSort);
	case SEQUENCE:
	    return getSequenceSort(elemSort);
	default:
	    return getSetSort(elemSort);
	}	    
    }

    private static CollectionSort getSetSort(OclSort elemSort) {

	if (elemSort == OclSort.OCLGENERIC) {
	    return OclSort.SET_OF_OCLGENERIC;
	} else if (elemSort == OclSort.OCLANY) {
	    return OclSort.SET_OF_OCLANY;
	} else if (elemSort == OclSort.OCLTYPE) {
	    return OclSort.SET_OF_OCLTYPE;
	} else if (elemSort == OclSort.BOOLEAN) {
	    return OclSort.SET_OF_BOOLEAN;
	} else if (elemSort == OclSort.REAL) {
	    return OclSort.SET_OF_REAL;
	} else if (elemSort == OclSort.INTEGER) {
	    return OclSort.SET_OF_INTEGER;
	} else if (elemSort == OclSort.STRING) {
	    return OclSort.SET_OF_STRING;
	} else {
	    return OclSort.SET_OF_CLASSIFIER;
	}
    }

    private static CollectionSort getBagSort(OclSort elemSort) {

	if (elemSort == OclSort.OCLGENERIC) {
	    return OclSort.BAG_OF_OCLGENERIC;
	} else if (elemSort == OclSort.OCLANY) {
	    return OclSort.BAG_OF_OCLANY;
	} else if (elemSort == OclSort.OCLTYPE) {
	    return OclSort.BAG_OF_OCLTYPE;
	} else if (elemSort == OclSort.BOOLEAN) {
	    return OclSort.BAG_OF_BOOLEAN;
	} else if (elemSort == OclSort.REAL) {
	    return OclSort.BAG_OF_REAL;
	} else if (elemSort == OclSort.INTEGER) {
	    return OclSort.BAG_OF_INTEGER;
	} else if (elemSort == OclSort.STRING) {
	    return OclSort.BAG_OF_STRING;
	} else {
	    return OclSort.BAG_OF_CLASSIFIER;
	}
    }

    private static CollectionSort getSequenceSort(OclSort elemSort) {

	if (elemSort == OclSort.OCLGENERIC) {
	    return OclSort.SEQUENCE_OF_OCLGENERIC;
	} else if (elemSort == OclSort.OCLANY) {
	    return OclSort.SEQUENCE_OF_OCLANY;
	} else if (elemSort == OclSort.OCLTYPE) {
	    return OclSort.SEQUENCE_OF_OCLTYPE;
	} else if (elemSort == OclSort.BOOLEAN) {
	    return OclSort.SEQUENCE_OF_BOOLEAN;
	} else if (elemSort == OclSort.REAL) {
	    return OclSort.SEQUENCE_OF_REAL;
	} else if (elemSort == OclSort.INTEGER) {
	    return OclSort.SEQUENCE_OF_INTEGER;
	} else if (elemSort == OclSort.STRING) {
	    return OclSort.SEQUENCE_OF_STRING;
	} else {
	    return OclSort.SEQUENCE_OF_CLASSIFIER;
	} 
    }
 
    /**
     * For finding out whether a certain sort is super- or subsort of another
     * sort or not, please use <code>extendsTrans</code>. 
     * Using <code>extendsSorts()</code> for this purpose may lead to 
     * undesired results when dealing with arraysorts! 
     * @return the sorts of the predecessors of this sort
     */
    public ImmutableSet<Sort> extendsSorts() {
	return DefaultImmutableSet.<Sort>nil();
    }

    /**
     * returns true iff the given sort is a transitive supersort of this sort
     * or it is the same.
     */
    public boolean extendsTrans(Sort sort) {
	if (sort instanceof OclGenericSort) {
	    return true;
	} else if (sort instanceof GenericSort) {
	    if (((GenericSort)sort).getOneOf().size() == 0) {
		return true;
	    } else {
            for (Sort sort1 : ((GenericSort) sort).getOneOf()) {
                if (this.extendsTrans(sort1)) {
                    return true;
                }
            }
		return false;
	    }
	} else {
	    if (!(sort instanceof CollectionSort)) {
		return false;
	    }
	    if (((CollectionSort)sort).getCollectionKind() != COLLECTION
		&& this.getCollectionKind() != ((CollectionSort)sort).getCollectionKind()) {
		return false;
	    }
	    return this.getElemSort().extendsTrans(((CollectionSort)sort).getElemSort());
	}
    }

    /** @return equality symbol of this sort */
    public Equality getEqualitySymbol() {
	return Op.EQUALS;
    }

    public boolean equals(Object obj) {
	if (!(obj instanceof CollectionSort)) {
	    return false;
	}
	CollectionSort cSort = (CollectionSort)obj;
        return this.collectionKind == cSort.collectionKind
                && this.elemSort == cSort.elemSort;
    }

    public int hashCode(){
	if (hashcode == 0) {
	    hashcode = calculateHash();
	}
	return hashcode;
    }

    protected int calculateHash(){
	int hashValue = 5;
	hashValue = hashValue*17 + collectionKind*5;  
	hashValue = hashValue*17 + elemSort.hashCode();
	return hashValue;
    }
    
    public String toString() {
	return name.toString();
    }
}
