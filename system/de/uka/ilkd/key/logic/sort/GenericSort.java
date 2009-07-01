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

/**
 * Sort used for generic taclets
 *
 * Within an SVInstantiations-object a generic sort is instantiated by
 * a concrete sort, which has to be a subsort of the instantiations of
 * the supersorts of this sort
 */
public class GenericSort extends AbstractNonCollectionSort 
    implements ObjectSort {
    

    /**
     * A possible instantiation of this generic sort by a concrete
     * sort must satisfy each of these conditions:
     *
     * - if any generic supersort is to be instantiated simultanously,
         then this instantiation has to be a supersort of the
         instantiation of this sort
     *
     * - the instantiation of this sort has to be a subsort of every
         concrete supersort
     *
     * - if "oneOf" is not empty, the instantiation must be an element
         of "oneOf"
     */
    private static final SetOfSort EMPTY_SORT_SET 
	= SetAsListOfSort.EMPTY_SET;

    /** direct supersorts */
    private SetOfSort        ext        = EMPTY_SORT_SET;
    /**
     * list of sorts this generic sort may be instantiated with;
     * EMPTY_SORT_SORT means that every sort may be used
     */
    private SetOfSort        oneOf      = EMPTY_SORT_SET;

    /**
     * creates a generic sort (with a new equality symbol for this
     * sort)   
     */
    public GenericSort(Name name) {
        super ( name );
    }

    /**
     * creates a generic sort
     * @param ext supersorts of this sort, which have to be either
     * concrete sorts or plain generic sorts (i.e. not collection
     * sorts of generic sorts)
     */
    public GenericSort( 
            Name             name,
            SetOfSort        ext,
	    SetOfSort        oneOf)
	throws GenericSupersortException {
	
        this ( name );
	this.ext        = ext;
	this.oneOf      = oneOf;
	checkSupersorts ();
    }

    private void checkSupersorts ()
	throws GenericSupersortException {
	IteratorOfSort it = extendsSorts ().iterator ();
	Sort           s, t;
	while ( it.hasNext () ) {
	    s = it.next ();
	    if ( s instanceof CollectionSort ) {
		t = ((CollectionSort)s).elementSort ();
		while ( t instanceof CollectionSort )
		    t = ((CollectionSort)t).elementSort ();
		if ( t instanceof GenericSort )
		    throw new GenericSupersortException
			( "Illegal supersort " + s +
			  " for generic sort " + name (),
			  s );
	    }
	}
    }

    /**
     * @return direct supersorts
     */
    public SetOfSort extendsSorts () {
	return ext;
    }

    /**
     * @return possible instantiations or "EMPTY_SORT_SET"
     */
    public SetOfSort getOneOf () {
	return oneOf;
    }

    /**
     * @return true if "p_s" is a possible instantiation of this
     * sort. This method does not check the instantiations of other
     * generic sorts, i.e. the return value true is possible even if
     * "p_s" is not a valid instantiation.
     *
     * Use "GenericSortInstantiations" instead
     */
    public boolean isPossibleInstantiation ( Sort p_s ) {
	return
	    p_s != Sort.FORMULA &&
	    ( oneOf.isEmpty() || oneOf.contains ( p_s ) ) &&
	    checkNonGenericSupersorts ( p_s );
    }

    /**
     * @return true iff "p_s" is subsort of every non-generic
     * supersort of this sort
     */
    protected boolean checkNonGenericSupersorts ( Sort p_s ) {
	IteratorOfSort it = ext.iterator ();
	Sort           ss;

	while ( it.hasNext () ) {
	    ss = it.next ();
	    if ( ss instanceof GenericSort ) {
		if ( !((GenericSort)ss).checkNonGenericSupersorts ( p_s ) )
		    return false;
	    } else {
		if ( !p_s.extendsTrans ( ss ) )
		    return false;
	    }
	}

	return true;
    }
}
