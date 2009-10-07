// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License.
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.collection;
/** tests non-destructive list implementation with String */

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
	    .prepend( new Integer ( 13 ) )
	    .prepend( new Integer ( 20 ) )
	    .prepend( new Integer ( 5 ) )
	    .prepend( new Integer ( 7 ) )
	    .prepend( new Integer ( 16 ) )
	    .prepend( new Integer ( 60 ) )
	    .prepend( new Integer ( 20 ) )
	    .prepend( new Integer ( -34 ) );
	b = ImmutableSLList.<Integer>nil()
	    .prepend( new Integer ( -1000 ) )
	    .prepend( new Integer ( 1000 ) )
	    .prepend( new Integer ( 8 ) );
    }

    public void testInsertElements() {
	ImmutableHeap<Integer> h = ImmutableLeftistHeap.<Integer>nilHeap();
	assertTrue("Empty heap should be empty",
		   h.isEmpty () && h.size () == 0);

	h.insert ( new Integer ( 1 ) );
	assertTrue("Empty heap should be empty",
		   h.isEmpty () && h.size () == 0);

	h = h.insert ( new Integer ( 1 ) );
	assertTrue("Heap should contain one element",
		   !h.isEmpty () && h.size () == 1 &&
		   h.findMin ().intValue () == 1);

	h = h.deleteMin ();
	assertTrue("Empty heap should be empty",
		   h.isEmpty () && h.size () == 0);

	h = h.insert ( new Integer ( 1 ) ).insert ( new Integer ( 2 ) );
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

    private ImmutableList<Integer> removeFirst ( ImmutableList<Integer> list, Integer element ) {
	ImmutableList<Integer> remainder = ImmutableSLList.<Integer>nil();
	Integer       i;

	while ( true ) {
	    assertTrue ( "Cannot remove element from list",
			 !list.isEmpty() );

	    i    = list.head ();
	    list = list.tail ();

	    if ( i.equals ( element ) )
		break;

	    remainder = remainder.prepend ( i );
	}

	return list.prepend ( remainder );
    }

    private boolean equals ( Iterator<Integer> t0, Iterator<Integer> t1 ) {
	ExtList l0 = new ExtList (), l1 = new ExtList ();

	while ( t0.hasNext () )
	    l0.add ( t0.next () );

	while ( t1.hasNext () )
	    l1.add ( t1.next () );

	Object[] a0 = (Object[])l0.collect ( Object.class );
	Object[] a1 = (Object[])l1.collect ( Object.class );

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
		       ( new Integer ( 123 ) ) );
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
	    l = l.prepend ( new Integer ( rand.nextInt ( 1000000 ) ) );

	h = h.insert ( l.iterator () );

	checkHeap ( l, h );
    }

}
