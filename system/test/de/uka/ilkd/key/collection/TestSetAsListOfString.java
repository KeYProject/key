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

import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.collection.ImmutableSet;
import java.util.Iterator;

/** tests non-destructive Set implementation with String */

public class TestSetAsListOfString extends junit.framework.TestCase {

    String str[]=new String[]{"Dies","ist","ein","Test"};

    public TestSetAsListOfString(String name) {
	super(name);
    }

    // test if String is SAME as one in the array arr
    private boolean isInArray(String str, String[] arr) {
        for (String anArr : arr) {
            if (anArr == str) {
                return true;
            }
        }
	return false;
    }


    // tests add and implicitly iterator, size
    public void testAdd() {
	ImmutableSet<String>[] newSet=new ImmutableSet[str.length+1];
	newSet[0]=DefaultImmutableSet.<String>nil();

	for (int i=1;i<str.length+1;i++) {
	    newSet[i]=newSet[i-1].add(str[i-1]);
	}
	// Test elements in set
	for (int i=0;i<str.length+1;i++) {
	    Iterator<String> it=newSet[i].iterator();
	    int size=newSet[i].size();
	    if (i>0) { // set should have elements
		assertTrue("Set has no elements, but should have some.",it.hasNext());
		assertTrue("Wrong cardinality",size==i);
	    } else { // set is empty
		assertTrue("Elements but set should be empty.",!it.hasNext());
		assertTrue("Wrong cardinality.",size==0);
	    }
	    int nr=0;
	    while (it.hasNext()) {
		assertTrue("Set has wrong elements",isInArray(it.next(),str));
		nr++;
	    }
	    // has right number of elements
	    assertTrue("Set has iterated to less/often",nr==size);
	}

	// add existing element, has to be SAME set
	assertSame("Element found 2 times in set or set is not the same.",newSet[str.length],newSet[str.length].add(str[0]));
    }

    // tests unify
    public void testUnion() {
	ImmutableSet<String>[] newSet=new ImmutableSet[str.length+1];
	newSet[0]=DefaultImmutableSet.<String>nil().add(str[0]).add(str[1]);
	newSet[1]=DefaultImmutableSet.<String>nil().add(str[1]).add(str[2]);
	// make the union of two sets and check if in the unions
	// appearance of str[1] == 1
	ImmutableSet<String> union=newSet[1].union(newSet[0]);
	assertTrue(union.size()==3);
	//test if set has all elements
	for (int i=0;i<3;i++) {
	    assertTrue(union.contains(str[0]));
	}
	// just to check that contains can say no too
	assertTrue(!union.contains(str[3]));
    }

    public void testUnionEmptyWithNonEmptySet() {
	ImmutableSet<String> empty = DefaultImmutableSet.<String>nil();
	ImmutableSet<String> hal = DefaultImmutableSet.<String>nil().add("H").add("a").add("l");
	
	assertEquals("Union of two sets should be symmetric", empty.union(hal), hal.union(empty));
	assertEquals("Wrong size.", empty.union(hal).size(), 3);
    }

    public void testUnionRemoveDuplicates() {
	ImmutableSet<String> hal = DefaultImmutableSet.<String>nil().add("H").add("a").add("l");
	ImmutableSet<String> lo = DefaultImmutableSet.<String>nil().add("l").add("o");
	
	assertEquals("Union of two sets should be symmetric", hal.union(lo), lo.union(hal));
	assertEquals("Wrong size.", hal.union(lo).size(), 4);
    }

    
    
    public void testSubset() {
	ImmutableSet<String> subSet=DefaultImmutableSet.<String>nil();
	ImmutableSet<String> superSet=DefaultImmutableSet.<String>nil();
	// subSet={Dies,ist}
	// superSet={Dies,ist,ein}
	subSet=subSet.add(str[0]).add(str[1]);
	superSet=subSet.add(str[2]);
	assertTrue("Failure: in subset relation (!sub<super)",subSet.subset(superSet));
	assertTrue("Failure: in subset relation (super<sub)",!superSet.subset(subSet));
	assertTrue("EmptySet is not part of another Set", DefaultImmutableSet.<String>nil().subset(superSet));
	assertTrue("A non empty set is subset of the empty set",!subSet.subset(DefaultImmutableSet.<String>nil()));
    }

    public void testRemove() {
	ImmutableSet<String> set=DefaultImmutableSet.<String>nil();
	// set={Dies,ist}
	set=set.add(str[0]).add(str[1]);
	assertTrue("Did not remove "+str[0]+" from list",
		   !(set.remove(str[0]).contains(str[0])));
    }


    public void testToString() {
	ImmutableSet<String> newSet=DefaultImmutableSet.<String>nil();
	for (int i=0;i<str.length;i++) {
 	    newSet=newSet.add(str[str.length-1-i]);
	}
	assertEquals("{Dies,ist,ein,Test}",newSet.toString());
    }


}
