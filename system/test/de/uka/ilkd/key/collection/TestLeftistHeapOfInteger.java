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


package de.uka.ilkd.key.collection;
/** tests non-destructive list implementation with String */

import de.uka.ilkd.key.collection.ImmutableHeap;
import de.uka.ilkd.key.collection.ImmutableLeftistHeap;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import java.util.Arrays;
import java.util.Iterator;
import java.util.Random;

import de.uka.ilkd.key.util.ExtList;

public class TestLeftistHeapOfInteger extends junit.framework.TestCase {

    public TestLeftistHeapOfInteger(String name) {
	super(name);
    }

    ImmutableList<Integer> a;
    ImmutableList<Integer> b;

    Random rand = new Random ();

    public void setUp() {
	a = ImmutableSLList.<Integer>nil()
	    .prepend( Integer.valueOf ( 13 ) )
	    .prepend( Integer.valueOf ( 20 ) )
	    .prepend( Integer.valueOf ( 5 ) )
	    .prepend( Integer.valueOf ( 7 ) )
	    .prepend( Integer.valueOf ( 16 ) )
	    .prepend( Integer.valueOf ( 60 ) )
	    .prepend( Integer.valueOf ( 20 ) )
	    .prepend( Integer.valueOf ( -34 ) );
	b = ImmutableSLList.<Integer>nil()
	   .prepend( Integer.valueOf ( -1000 ) )
	   .prepend( Integer.valueOf ( 1000 ) )
	   .prepend( Integer.valueOf ( 8 ) );
    }

    public void testInsertElements() {
	ImmutableHeap<Integer> h = ImmutableLeftistHeap.<Integer>nilHeap();
	assertTrue("Empty heap should be empty",
		   h.isEmpty () && h.size () == 0);
	
	h.insert ( Integer.valueOf ( 1 ) );
	assertTrue("Empty heap should be empty",
		   h.isEmpty () && h.size () == 0);

	h = h.insert ( Integer.valueOf ( 1 ) );
	assertTrue("Heap should contain one element",
		   !h.isEmpty () && h.size () == 1 &&
		   h.findMin ().intValue () == 1);

	h = h.deleteMin ();
	assertTrue("Empty heap should be empty",
		   h.isEmpty () && h.size () == 0);

	h = h.insert ( Integer.valueOf ( 1 ) ).insert ( Integer.valueOf ( 2 ) );
	assertTrue("Heap should contain two elements",
		   !h.isEmpty () && h.size () == 2 &&
		   h.findMin ().intValue () == 1 );
	h = h.deleteMin ();
	assertTrue("Heap should contain one element",
		   !h.isEmpty () && h.size () == 1 &&
		   h.findMin ().intValue () == 2);
	h = h.deleteMin ();
	assertTrue("Empty heap should be empty",
		   h.isEmpty () && h.size () == 0);
    }

    private boolean equals ( Iterator<Integer> t0, Iterator<Integer> t1 ) {
	ExtList l0 = new ExtList (), l1 = new ExtList ();

	while ( t0.hasNext () )
	    l0.add ( t0.next () );

	while ( t1.hasNext () )
	    l1.add ( t1.next () );

	Object[] a0 = l0.collect ( Object.class );
	Object[] a1 = l1.collect ( Object.class );

	Arrays.sort ( a0 );
	Arrays.sort ( a1 );

	return Arrays.equals ( a0, a1 );
    }

    private void checkHeap( ImmutableList<Integer> elements, ImmutableHeap<Integer> h ) {
	assertTrue ( "Heap has incorrect size",
		     h.size () == elements.size () &&
		     ( h.size () == 0 ) == h.isEmpty () );

	assertTrue ( "Unsorted heap iterator does not return the right elements",
		     equals ( h.iterator (), elements.iterator () ) );

	Iterator<Integer> t0           = h.sortedIterator ();
	Integer           lastElement  = null;
	Integer           element;

	while ( t0.hasNext () ) {
	    element = t0.next ();
	    if ( lastElement != null )
		assertTrue ( "Elements returned by sorted iterator should be sorted",
			     lastElement.compareTo( element ) <= 0 );
	    lastElement = element;
	}

	assertTrue ( "Unsorted heap iterator does not return the right elements",
		     equals ( h.sortedIterator (), elements.iterator () ) );

	ImmutableList<Integer> list = ImmutableSLList.<Integer>nil();
	lastElement = null;

	while ( !h.isEmpty () ) {
	    element = h.findMin ();
	    list    = list.prepend ( element );
	    if ( lastElement != null )
		assertTrue ( "Elements returned by findMin() should be sorted",
			     lastElement.compareTo( element ) <= 0 );
	    lastElement = element;
	    h = h.deleteMin ();
	}

	assertTrue ( "findMin does not return the right elements",
		     equals ( list.iterator (), elements.iterator () ) );
    }

    private ImmutableHeap<Integer> removeAll ( ImmutableHeap<Integer> h, Iterator<Integer> elements ) {
	while ( elements.hasNext () )
	    h = h.removeAll ( elements.next () );
	return h;
    }

    public void testInsertIterator() {
	ImmutableHeap<Integer> h = ImmutableLeftistHeap.<Integer>nilHeap();

	h = h.insert ( ImmutableSLList.<Integer>nil().iterator () );
	checkHeap ( ImmutableSLList.<Integer>nil(), h );
	assertTrue("Empty heap should be empty",
		   h.isEmpty () && h.size () == 0);

	h = h.insert ( a.iterator () );
	checkHeap ( a, h );

	h = h.insert ( a.iterator () );
	checkHeap ( a.prepend( a ), h );

	h = h.insert ( ImmutableSLList.<Integer>nil().iterator () );
	checkHeap ( a.prepend( a ), h );

	h = h.insert ( h.iterator () );
	checkHeap ( a.prepend( a ).prepend( a ).prepend( a ), h );

	h = h.insert ( h.sortedIterator () );
	checkHeap ( a.prepend( a ).prepend( a ).prepend( a )
		    .prepend( a ).prepend( a ).prepend( a ).prepend( a ), h );
    }

    public void testInsertHeap() {
	ImmutableHeap<Integer> h = ImmutableLeftistHeap.<Integer>nilHeap();

	h = h.insert ( a.iterator () );
	checkHeap ( a, h );

	h = h.insert ( ImmutableLeftistHeap.<Integer>nilHeap() );
	checkHeap ( a, h );

	h = h.insert ( h );
	checkHeap ( a.prepend( a ), h );

	h = h.insert ( ImmutableLeftistHeap.<Integer>nilHeap().insert
		       ( Integer.valueOf ( 123 ) ) );
	checkHeap ( a.prepend( a ).prepend ( new Integer ( 123 ) ), h );
    }

    public void testRemoveAll () {
	ImmutableHeap<Integer> h = ImmutableLeftistHeap.<Integer>nilHeap();

	// Test removal of all elements (from empty heap)
	checkHeap ( ImmutableSLList.<Integer>nil(), removeAll( h, a.iterator () ) );

	h = h.insert ( a.iterator () );
	checkHeap ( a, h );

	// Test removal of arbitrary elements
	checkHeap ( a.removeAll( a.head () ), h.removeAll( a.head () ) );

	// Test removal of all elements
	checkHeap ( ImmutableSLList.<Integer>nil(), removeAll( h, a.iterator () ) );

	// Test removal of non-existing elements
	assertSame ( "Heap should not be different",
		    h, removeAll ( h, b.iterator () ) );
    }

    public void testLargeHeap () {
	ImmutableHeap<Integer> h = ImmutableLeftistHeap.<Integer>nilHeap();
	ImmutableList<Integer> l = ImmutableSLList.<Integer>nil();

	int i = 1000;
	while ( i-- != 0 )
	    l = l.prepend ( Integer.valueOf ( rand.nextInt ( 1000000 ) ) );

	h = h.insert ( l.iterator () );

	checkHeap ( l, h );
    }

}
