// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.proof.incclosure;

import java.util.Iterator;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.util.Debug;


/**
 * Class for merging an arbitrary number of constraint streams
 */
public class MultiMerger implements Merger {

    /**
     * BinaryMerger are arranged as a balanced binary tree with
     * rootMerger being the root and leafSinks a list of the leafs'
     * sinks
     */
    private BinaryMerger rootMerger;
    private ImmutableList<Sink>   leafSinks  = ImmutableSLList.<Sink>nil();

    private int          arity      = 0;

    /**
     * Parent sink within the tree of sinks
     */
    private Sink         parent;
    
    /**
     * Services eg. if necessary additional sorts are added
     * (this can happen during unification)
     */
    private Services services;
    
    /**
     * Initial value of the buffers will be the parent's value
     */
    public MultiMerger ( Sink p_parent,
			 int  p_arity,
                         Services p_services ) {
	Debug.assertTrue ( p_arity >= 2,
			   "Tried to create MultiMerger with less than 2 sinks" );

	parent = p_parent;
        services = p_services;
	expand ( p_arity );
    }

    /**
     * Expand the merger, possibly adding new sinks. The old sinks
     * will remain valid and will be the first elements in the new
     * list of all sinks. It is much more efficient to create all
     * needed sinks by a single call than by successive calls.
     */
    public void expand ( int p_arity ) {
	if ( p_arity == arity )
	    return;

	Debug.assertTrue ( p_arity > arity,
			   "Tried to shrink MultiMerger" );	
	
	BinaryMerger   r        = new BinaryMerger ( parent, services );
	ImmutableList<Sink>     sinkList = ImmutableSLList.<Sink>nil();
	ImmutableList<Sink>     newList  = ImmutableSLList.<Sink>nil();
	Iterator<Sink> it;
	int            i;

	it       = r.getSinks ();
	sinkList = sinkList.append ( it.next () ).append ( it.next () );

	if ( arity == 0 )
	    i = p_arity - 2;
	else {
	    i = p_arity - arity - 1;
	    rootMerger.setParent ( sinkList.head () );
	    sinkList = sinkList.tail ();	    
	}

	rootMerger = r;
	arity      = p_arity;

	while ( i-- != 0 ) {
	    if ( sinkList.isEmpty() ) {
		/** Increase the depth of the tree by one */
		while ( !newList.isEmpty() ) {
		    sinkList = sinkList.prepend ( newList.head () );
		    newList  = newList.tail ();
		}
	    }

	    it       = new BinaryMerger ( sinkList.head (), services ).getSinks ();
	    newList  = newList.prepend ( it.next () ).prepend ( it.next () );
	    sinkList = sinkList.tail ();
	}

	while ( !newList.isEmpty() ) {
	    sinkList = sinkList.prepend ( newList.head () );
	    newList  = newList.tail ();
	}
	
	while ( !sinkList.isEmpty() ) {
	    leafSinks = leafSinks.append ( sinkList.head () );
	    sinkList  = sinkList.tail ();
	}
    }

    public int  getArity () {
	return arity;
    }

    /**
     * Inputs offered by this merger
     */
    public Iterator<Sink> getSinks () {
	return leafSinks.iterator ();
    }

    /**
     * @return true iff the whole subtree of sinks below this merger
     * has seen consistent constraints
     */
    public boolean        isSatisfiable () {
	return rootMerger.isSatisfiable ();
    }

    /**
     * Reparent this merger; an implementing class should make
     * appropriate "reset"-calls to the new parent
     */
    public void           setParent     ( Sink p_parent ) {
	parent = p_parent;
	rootMerger.setParent ( parent );
    }

}
