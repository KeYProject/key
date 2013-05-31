// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
// 


package de.uka.ilkd.key.logic.sort;

import java.util.Iterator;

import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.logic.Name;

/**
 * Sort used for generic taclets
 *
 * Within an SVInstantiations-object a generic sort is instantiated by
 * a concrete sort, which has to be a subsort of the instantiations of
 * the supersorts of this sort
 */
public final class GenericSort extends AbstractSort {
    

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

    
    /**
     * list of sorts this generic sort may be instantiated with;
     * EMPTY_SORT_SORT means that every sort may be used
     */
    private final ImmutableSet<Sort> oneOf;
    
   /**
     * creates a generic sort
     * @param ext supersorts of this sort, which have to be either
     * concrete sorts or plain generic sorts (i.e. not collection
     * sorts of generic sorts)
     */
    public GenericSort( 
            Name             name,
            ImmutableSet<Sort>        ext,
	    ImmutableSet<Sort>        oneOf)
		throws GenericSupersortException {
        super(name, ext, false);
	this.oneOf = oneOf;
	checkSupersorts();
    }

 
    public GenericSort(Name name) {
	super(name, DefaultImmutableSet.<Sort>nil(), false);
	this.oneOf = DefaultImmutableSet.<Sort>nil();
    }

 
    private void checkSupersorts ()
	throws GenericSupersortException {
	Iterator<Sort> it = extendsSorts ().iterator ();
	Sort           s, t;
	while ( it.hasNext () ) {
	    s = it.next ();
	    if ( s instanceof ArraySort ) {
		t = ((ArraySort)s).elementSort ();
		while ( t instanceof ArraySort )
		    t = ((ArraySort)t).elementSort ();
		if ( t instanceof GenericSort )
		    throw new GenericSupersortException
			( "Illegal supersort " + s +
			  " for generic sort " + name (),
			  s );
	    }
	}
    }

    /**
     * @return possible instantiations
     */
    public ImmutableSet<Sort> getOneOf () {
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
	Iterator<Sort> it =  extendsSorts().iterator ();
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
