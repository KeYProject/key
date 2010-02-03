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
/** tests non-destructive Set implementation with String */

public class TestSetAsListOfString extends junit.framework.TestCase {

    String str[]=new String[]{"Dies","ist","ein","Test"};

    public TestSetAsListOfString(String name) {
	super(name);
    }

    // test if String is SAME as one in the array arr
    private boolean isInArray(String str, String[] arr) {
	for (int i=0;i<arr.length;i++) {
	    if (arr[i]==str) {
		return true;
	    }
	}
	return false;
    }


    // tests add and implicitly iterator, size 
    public void testAdd() {
	SetOfString[] newSet=new SetOfString[str.length+1];
	newSet[0]=SetAsListOfString.EMPTY_SET;
	
	for (int i=1;i<str.length+1;i++) {
	    newSet[i]=newSet[i-1].add(str[i-1]);	    
	}
	// Test elements in set
	for (int i=0;i<str.length+1;i++) {
	    IteratorOfString it=newSet[i].iterator();
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
    public void testUnify() {
	SetOfString[] newSet=new SetOfString[str.length+1];
	newSet[0]=(SetAsListOfString.EMPTY_SET.add(str[0])).add(str[1]);
	newSet[1]=SetAsListOfString.EMPTY_SET.add(str[1]).add(str[2]);	    
	// make the union of two sets and check if in the unions
	// appearance of str[1] == 1   
	SetOfString union=newSet[1].union(newSet[0]);
	assertTrue(union.size()==3);
	//test if set has all elements 
	for (int i=0;i<3;i++) {	
	    assertTrue(union.contains(str[0]));
	}
	// just to check that contains can say no too
	assertTrue(!union.contains(str[3]));
    }

    public void testSubset() {
	SetOfString subSet=SetAsListOfString.EMPTY_SET;
	SetOfString superSet=SetAsListOfString.EMPTY_SET;
	// subSet={Dies,ist}
	// superSet={Dies,ist,ein}
	subSet=subSet.add(str[0]).add(str[1]);
	superSet=subSet.add(str[2]);
	assertTrue("Failure: in subset relation (!sub<super)",subSet.subset(superSet));
	assertTrue("Failure: in subset relation (super<sub)",!superSet.subset(subSet));
	assertTrue("EmptySet is not part of another Set", (SetAsListOfString.EMPTY_SET).subset(superSet));
	assertTrue("A non empty set is subset of the empty set",!subSet.subset(SetAsListOfString.EMPTY_SET));
    }

    public void testRemove() {
	SetOfString set=SetAsListOfString.EMPTY_SET;
	// set={Dies,ist}
	set=set.add(str[0]).add(str[1]);
	assertTrue("Did not remove "+str[0]+" from list",
		   !(set.remove(str[0]).contains(str[0])));
    }


    public void testToString() {
	SetOfString newSet=SetAsListOfString.EMPTY_SET;	
	for (int i=0;i<str.length;i++) {
 	    newSet=newSet.add(str[str.length-1-i]);	    
	}	
	assertEquals("{Dies,ist,ein,Test}",newSet.toString());
    }


}
