// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
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
import java.util.Random;

import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.util.ExtList;

public class TestLeftistHeapOfInteger extends junit.framework.TestCase {

    public TestLeftistHeapOfInteger(String name) {
	super(name);
    }

    ListOfInteger a;
    ListOfInteger b;

    Random rand = new Random ();
    
    public void setUp() {
	a = SLListOfInteger.EMPTY_LIST
	    .prepend( new Integer ( 13 ) )
	    .prepend( new Integer ( 20 ) )
	    .prepend( new Integer ( 5 ) )
	    .prepend( new Integer ( 7 ) )
	    .prepend( new Integer ( 16 ) )
	    .prepend( new Integer ( 60 ) )
	    .prepend( new Integer ( 20 ) )
	    .prepend( new Integer ( -34 ) );
	b = SLListOfInteger.EMPTY_LIST
	    .prepend( new Integer ( -1000 ) )
	    .prepend( new Integer ( 1000 ) )
	    .prepend( new Integer ( 8 ) );
    }

    public void testInsertElements() {
	HeapOfInteger h = LeftistHeapOfInteger.EMPTY_HEAP;
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

    private ListOfInteger removeFirst ( ListOfInteger list, Integer element ) {
	ListOfInteger remainder = SLListOfInteger.EMPTY_LIST;
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

    private boolean equals ( IteratorOfInteger t0, IteratorOfInteger t1 ) {
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

    private void checkHeap( ListOfInteger elements, HeapOfInteger h ) {
	assertTrue ( "Heap has incorrect size",
		     h.size () == elements.size () &&
		     ( h.size () == 0 ) == h.isEmpty () );

	assertTrue ( "Unsorted heap iterator does not return the right elements",
		     equals ( h.iterator (), elements.iterator () ) );

	IteratorOfInteger t0           = h.sortedIterator ();
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

	ListOfInteger list = SLListOfInteger.EMPTY_LIST;
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

    private HeapOfInteger removeAll ( HeapOfInteger h, IteratorOfInteger elements ) {
	while ( elements.hasNext () )
	    h = h.removeAll ( elements.next () );
	return h;
    }

    public void testInsertIterator() {
	HeapOfInteger h = LeftistHeapOfInteger.EMPTY_HEAP;

	h = h.insert ( SLListOfInteger.EMPTY_LIST.iterator () );
	checkHeap ( SLListOfInteger.EMPTY_LIST, h );
	assertTrue("Empty heap should be empty",
		   h.isEmpty () && h.size () == 0);
	
	h = h.insert ( a.iterator () );	
	checkHeap ( a, h );

	h = h.insert ( a.iterator () );	
	checkHeap ( a.prepend( a ), h );

	h = h.insert ( SLListOfInteger.EMPTY_LIST.iterator () );
	checkHeap ( a.prepend( a ), h );
	
	h = h.insert ( h.iterator () );
	checkHeap ( a.prepend( a ).prepend( a ).prepend( a ), h );

	h = h.insert ( h.sortedIterator () );
	checkHeap ( a.prepend( a ).prepend( a ).prepend( a )
		    .prepend( a ).prepend( a ).prepend( a ).prepend( a ), h );
    }

    public void testInsertHeap() {
	HeapOfInteger h = LeftistHeapOfInteger.EMPTY_HEAP;

	h = h.insert ( a.iterator () );	
	checkHeap ( a, h );

	h = h.insert ( LeftistHeapOfInteger.EMPTY_HEAP );
	checkHeap ( a, h );

	h = h.insert ( h );
	checkHeap ( a.prepend( a ), h );

	h = h.insert ( LeftistHeapOfInteger.EMPTY_HEAP.insert
		       ( new Integer ( 123 ) ) );
	checkHeap ( a.prepend( a ).prepend ( new Integer ( 123 ) ), h );
    }
 
    public void testRemoveAll () {
	HeapOfInteger h = LeftistHeapOfInteger.EMPTY_HEAP;

	// Test removal of all elements (from empty heap)
	checkHeap ( SLListOfInteger.EMPTY_LIST, removeAll( h, a.iterator () ) );

	h = h.insert ( a.iterator () );	
	checkHeap ( a, h );

	// Test removal of arbitrary elements
	checkHeap ( a.removeAll( a.head () ), h.removeAll( a.head () ) );

	// Test removal of all elements
	checkHeap ( SLListOfInteger.EMPTY_LIST, removeAll( h, a.iterator () ) );

	// Test removal of non-existing elements
	assertSame ( "Heap should not be different",
		    h, removeAll ( h, b.iterator () ) );
    }
   
    public void testLargeHeap () {
	HeapOfInteger h = LeftistHeapOfInteger.EMPTY_HEAP;
	ListOfInteger l = SLListOfInteger.EMPTY_LIST;

	int i = 1000;
	while ( i-- != 0 )
	    l = l.prepend ( new Integer ( rand.nextInt ( 1000000 ) ) );

	h = h.insert ( l.iterator () );

	checkHeap ( l, h );
    }

}
