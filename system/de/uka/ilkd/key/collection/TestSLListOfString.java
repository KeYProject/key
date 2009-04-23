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

public class TestSLListOfString extends junit.framework.TestCase {

    String str[]=new String[]{"Dies","ist","ein","Test"};

    public TestSLListOfString(String name) {
	super(name);
    }

    ListOfString a;   // "A" "B" "C"
    ListOfString a1;  // "A" "B" "C"
    ListOfString b;   // "A" "B"
    ListOfString c;   // "A" "B" "C" "D"
    ListOfString d;   // "A" "B" "A"
    ListOfString e;   // "A" "B" null
    ListOfString e1;   // "A" "B" null


    public void setUp() {
	a = SLListOfString.EMPTY_LIST
	    .prepend("C").prepend("B").prepend("A");
	a1 = SLListOfString.EMPTY_LIST
	    .prepend("C").prepend("B").prepend("A");
	b = SLListOfString.EMPTY_LIST
	    .prepend("B").prepend("A");
	c = SLListOfString.EMPTY_LIST
	    .prepend("D").prepend("C").prepend("B").prepend("A");
	d = SLListOfString.EMPTY_LIST
	    .prepend("A").prepend("B").prepend("A");
	e = SLListOfString.EMPTY_LIST
	    .prepend((String)null).prepend("B").prepend("A");
	e1 = SLListOfString.EMPTY_LIST
	    .prepend((String)null).prepend("B").prepend("A");
    }

    // tests prepend and implicitly iterator, size 
    public void testPrepend() {
	ListOfString[] newList=new ListOfString[str.length+1];
	newList[0]=SLListOfString.EMPTY_LIST;
	
	for (int i=1;i<str.length+1;i++) {
	    newList[i]=newList[i-1].prepend(str[i-1]);	    
	}
	// Test elements in list
	for (int i=0;i<str.length+1;i++) {
	    IteratorOfString it=newList[i].iterator();
	    int size=newList[i].size();
	    if (i>0) { // list should have elements 
		assertTrue(it.hasNext());
		assertTrue(size==i);
	    } else { // list is empty
		assertTrue(!it.hasNext());
		assertTrue(size==0);
	    }	    
	    int nr=0;
	    while (it.hasNext()) {
		assertSame(it.next(),str[size-1-nr]);	    
		nr++;
	    }
	    // list has right length
	    assertTrue(nr==size);
	}
	// prepend two lists
	ListOfString prepList=newList[1].prepend(newList[2]);
	assertTrue(prepList.size()==3);
	// right order
	assertEquals(str[1],prepList.head());
	assertEquals(str[0],prepList.tail().head());
	assertEquals(str[0],prepList.tail().tail().head());
    }

    // tests append and implicitly iterator, size 
    public void testAppend() {
	ListOfString[] newList=new ListOfString[str.length+1];
	newList[0]=SLListOfString.EMPTY_LIST;
	
	for (int i=1;i<str.length+1;i++) {
	    newList[i]=newList[i-1].append(str[i-1]);	    
	}
	// Test elements in list
	for (int i=0;i<str.length+1;i++) {	    
	    IteratorOfString it=newList[i].iterator();
	    int size=newList[i].size();
	    if (i>0) { // list should have elements 
		assertTrue(it.hasNext());
		assertTrue(size==i);
	    } else { // list is empty
		assertTrue(!it.hasNext());
		assertTrue(size==0);
	    }	    
	    int nr=0;
	    while (it.hasNext()) {
		assertSame(it.next(),str[nr]);	    
		nr++;
	    }
	    // list has right length
	    assertTrue(nr==size);
	}

	// append two lists
	ListOfString appList=newList[2].append(newList[1]);
	assertTrue(appList.size()==3);
	// right order
	assertEquals(str[0],appList.head());
	assertEquals(str[1],appList.tail().head());
	assertEquals(str[0],appList.tail().tail().head());
    }

    // tests tail,head
    public void testHeadTail() {
	ListOfString[] newList=new ListOfString[str.length+1];
	newList[0]=SLListOfString.EMPTY_LIST;	

	for (int i=1;i<str.length+1;i++) {
	    newList[i]=newList[i-1].prepend(str[i-1]);	    
	}	
	// test cascading tail
	for (int i=0;i<str.length;i++) {
	    assertSame(newList[i+1].tail(),newList[i]);
	    assertSame(newList[i+1].head(),str[i]);
	}	
    }

   // tests contains
    public void testContains() {
	ListOfString newList=SLListOfString.EMPTY_LIST;	

	for (int i=1;i<str.length+1;i++) {
	    newList=newList.append(str[i-1]);	    
	}	
	// test cascading tail
	for (int i=0;i<str.length;i++) {
	    assertTrue(newList.contains(str[i]));
	}	
    }


  // tests removeAll
    public void testRemoveAll() {
	ListOfString newList=SLListOfString.EMPTY_LIST;	

	newList=newList.append(str[0]);
	for (int i=1;i<str.length+1;i++) {
	    newList=newList.append(str[i-1]);	    
	}	
	newList=newList.append(str[0]);
	newList=newList.removeAll(str[0]);
	assertTrue("str[0] should have been removed",!newList.contains(str[0]));

    }   

    public void testRemoveFirst() {
	ListOfString newList=SLListOfString.EMPTY_LIST;	
	
	newList=newList.prepend(str[0]);
	for (int i=1;i<str.length+1;i++) {
	    newList=newList.prepend(str[i-1]);	    
	}	
	newList=newList.prepend(str[0]);
	int oldSize = newList.size();
	newList=newList.removeFirst(str[0]);


	assertTrue("Only first occurrence should have been removed", newList.head() != str[0] && newList.size() == oldSize - 1);

	newList=newList.removeFirst(str[0]);
	assertTrue("Only first occurrence should have been removed", newList.size() == oldSize - 2);
	newList=newList.removeFirst(str[0]);

	assertTrue("Only first occurrence should have been removed", !(newList.contains(str[0])) && newList.size() == oldSize - 3);

    }   

    public void testEquals() {
	assertTrue("a==a1",a.equals(a1));
	assertTrue("a!=b",! a.equals(b));
	assertTrue("a!=c",! a.equals(c));
	assertTrue("a!=d",! a.equals(d));
	assertTrue("a!=e",! a.equals(e));
	assertTrue("e!=a",! e.equals(a));
	assertTrue("e==e1", e.equals(e1));
    }
    

    public void testToString() {
	ListOfString newList=SLListOfString.EMPTY_LIST;	
	for (int i=0;i<str.length;i++) {
	    newList=newList.append(str[i]);	    
	}	
	assertEquals("[Dies,ist,ein,Test]",newList.toString());
    }


    public static void performanceTest(int n) {
	System.out.println("Performance Test for " + n + " elements");
	ListOfString newList=SLListOfString.EMPTY_LIST;	
	System.out.println("Create list with prepend.");
	long start = System.currentTimeMillis();
	for (int i = 0; i<n; i++) {
	    newList = newList.prepend(""+i);
	}
	long end = System.currentTimeMillis();
	System.out.println("Time:" + (end-start) +" ms");

	System.out.print("append:");
	start = System.currentTimeMillis();
	for (int i = 0; i<n; i++) {
	    newList = newList.append(""+i);
	}
	end = System.currentTimeMillis();
	System.out.println((end-start) +" ms");

 	System.out.print("contains:");
 	start = System.currentTimeMillis();
 	newList.contains("" + n);
 	end = System.currentTimeMillis();
 	System.out.println((end-start) +" ms");

    }


    public static void main(String[] args) {
	ListOfString newList=SLListOfString.EMPTY_LIST;	
	newList.prepend("a");
	
 	performanceTest(10);
 	performanceTest(100);
 	performanceTest(1000);
 	performanceTest(10000);
 	performanceTest(100000);
 	performanceTest(1000000);	
    }
}
