// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.asmkey.util.graph;

import java.util.NoSuchElementException;

import junit.framework.TestCase;
import de.uka.ilkd.asmkey.util.TestUtil.Item;
import de.uka.ilkd.key.logic.IteratorOfNamed;
import de.uka.ilkd.key.logic.Named;

public class TestTopologicalOrder extends TestCase {

    private AcyclicDependancyGraph graph;
    private Item[] is;

    public void testTopologicalOrderLinear() throws GraphException, CycleException {
	TopologicalOrder order;
	IteratorOfNamed it;
	graph = new AcyclicDependancyGraph();
	is = new Item[10];
	order = new TopologicalOrder(graph);

	GraphUtil.populateItemsAndGraph(is, graph);
	for(int i=1; i<is.length; i++) {
	    graph.addEdge(is[i-1], is[i]);
	}
	
	it = order.topologicalOrder();
	for(int i = 0; i<is.length; i++) {
	    try {
		assertItemsEquals(i, it.next());
	    }
	    catch (NoSuchElementException e) {
		fail("The iterator has not enough elements: i=" + i);
	    }
	}
	assertFalse("The iterator should have no more elements.", it.hasNext());

	it = order.reverseTopologicalOrder();
	for(int i = is.length-1; i>=0; i--) {
	    try {
		assertItemsEquals(i, it.next());
	    }
	    catch (NoSuchElementException e) {
		fail("The iterator has not enough elements: i=" + i);
	    }
	}
	assertFalse("The iterator should have no more elements.", it.hasNext());
    }

    public void testTopologicalOrderDiamond() throws GraphException, CycleException {
	TopologicalOrder order;
	IteratorOfNamed it;
	graph = new AcyclicDependancyGraph();
	is = new Item[10];
	order = new TopologicalOrder(graph);

	GraphUtil.populateItemsAndGraph(is, graph);
	for(int i=0; i<is.length; i++) {
	    switch(i%3) {
	    case 0:
		if(i!=9) {
		    graph.addEdge(is[i], is[i+1]);
		    graph.addEdge(is[i], is[i+2]);
		}
		break;
	    case 1:
		graph.addEdge(is[i], is[i+2]);
		break;
	    case 2:
		graph.addEdge(is[i], is[i+1]);
		break;
	    }
	}

	// it = order.topologicalOrder();
// 	while(it.hasNext()) { System.out.println(it.next().name().toString());}
// 	assertTrue("edge I7 to I9 should exist.", graph.containsEdge(is[7], is[9]));
	it = order.topologicalOrder();
	
	boolean already1 = false;
	for(int i=0; i<is.length; i++) {
	    try {
		Named item = it.next();

		switch(i%3) {
		case 0:
		    assertItemsEquals(i, item);
		    break;
		case 1:
		    if (item==is[i]) {
			already1=true;
		    } else {
			assertItemsEquals(i+1, item);
		    }
		    break;
		case 2:
		    if (already1) {
			assertItemsEquals(i, item);
			already1 = false;
		    } else {
			assertItemsEquals(i-1, item);
		    }
		    break;
		}
	    }
	    catch (NoSuchElementException e) {
		fail("The iterator has not enough elements: i=" + i);
	    }
	}
	assertFalse("The iterator should have no more elements.", it.hasNext());
	
    }

    public void testBaseConfiguration() throws GraphException, CycleException {
	TopologicalOrder order;
	IteratorOfNamed it;
	graph = new AcyclicDependancyGraph();
	is = new Item[10];
	order = new TopologicalOrder(graph);

	GraphUtil.populateItemsAndGraph(is, graph);
	for(int i=is.length-1; i>=0; i--) {
	    for(int j=0; j<i; j++) {
		graph.addEdge(is[i], is[j]);
	    }
	}
	
	it = order.reverseTopologicalOrder();
	for(int i = 0; i<is.length; i++) {
	    try {
		assertItemsEquals(i, it.next());
	    }
	    catch (NoSuchElementException e) {
		fail("The iterator has not enough elements: i=" + i);
	    }
	}
	assertFalse("The iterator should have no more elements.", it.hasNext());
    }

    private void assertItemsEquals(int i, Named item) {
	assertEquals("The " + i + "th elements should be the same " +
		     "in the array and in the iterator", is[i], item);
    }

}

