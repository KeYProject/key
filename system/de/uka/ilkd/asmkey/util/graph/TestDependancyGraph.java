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

import junit.framework.TestCase;
import de.uka.ilkd.asmkey.util.TestUtil.Item;

/**
 * To test the dependancy graph class
 * we test the basic properties, like adding
 * and removing vertices, testing membership, etc....
 */
public class TestDependancyGraph extends TestCase {

    private DependancyGraph graph;
    private Item[] is;

    public void testDependancyGraph1() {
	graph = new DependancyGraph();
	
	Item[] is = createNewItems(5);

	/* first we insert the elements */
	for(int i=0; i<is.length; i++) {
	    addAndOk(is[i], "Problem, cannot add " + is[i]);
	}
	assertSize(5);
	
	/* we try to reinsert them */
	addAndException(is, "is");
	assertSize(5);

	/* we create new items with the same names and
	 * try to insert them: it should fail
	 */
	Item os[] = createNewItems(5);
	addAndException(os, "os");
	assertSize(5);
	
	/* then we control existence and retrieval of
	 * the elements
	 */
	assertContainsItem(is);
	retrieveItems(is);
	
	/* we create some edges */
	Edge[] edges = new Edge[10];
	edges[0] = new Edge(is[0], is[1]);
	edges[1] = new Edge(is[0], is[2]);
	edges[2] = new Edge(is[1], is[2]);
	edges[3] = new Edge(is[2], is[1]);
	edges[4] = new Edge(is[3], is[1]);
	edges[5] = new Edge(is[3], is[2]);
	edges[6] = new Edge(is[3], is[4]);
	edges[7] = new Edge(is[3], is[0]);
	edges[8] = new Edge(is[4], is[0]);
	edges[9] = new Edge(is[4], is[4]);
	
	/* we add, recheck vertices, and check edges */
	addEdgesAndOk(edges);
	assertSize(5);
	assertContainsItem(is);
	retrieveItems(is);
	assertContainsEdges(edges);

	/* we readd, rerecheck vertices and check edges */
	addEdgesAndOk(edges);
	assertSize(5);
	assertContainsItem(is);
	retrieveItems(is);
	assertContainsEdges(edges);

	/* we create some non-existant edges and
	 * check they do not exists
	 */
	Edge[] failEdges = new Edge[5];
	failEdges[0] = new Edge(is[0], is[3]);
	failEdges[1] = new Edge(is[1], is[4]);
	failEdges[2] = new Edge(is[3], is[3]);
	failEdges[3] = new Edge(is[2], is[3]);
	failEdges[4] = new Edge(is[4], is[1]);
	for(int i=0; i<failEdges.length; i++) {
	    assertFalse("The edge " + failEdges[i] + " should not exists in the graph",
			i%2==0?graph.containsEdge(failEdges[i]):
			graph.containsEdge(failEdges[i].start, failEdges[i].end));
	}

	//TEST TO FINISH: test remove and iterator.

    }

    public void testDependancyGraph2() {
	graph = new DependancyGraph();

	is = new Item[11];

	for(int i=0;i<is.length; i++) {
	    is[i] = new Item("I" + i);
	}

	Edge[] edges= new Edge[] {
	    new Edge(is[0], is[1]),
	    new Edge(is[0], is[2]),
	    new Edge(is[1], is[2]),
	    new Edge(is[1], is[3]),
	    new Edge(is[2], is[4]),
	    new Edge(is[10],is[0]),
	    new Edge(is[8], is[6]),
	    new Edge(is[4], is[5]),
	    new Edge(is[5], is[9]),
	    new Edge(is[9], is[6]),
	    new Edge(is[7], is[10])
	};

	addEdgesAndOk(edges);
	assertContainsEdges(edges);
    }

    private Item[] createNewItems(int size) {
	Item[] items = new Item[size];
	for(int i=0;i<size;) {
	    items[i] = new Item("U" + (++i));
	}
	return items;
    }

    private void assertSize(int i) {
	assertEquals("The size of the graph is not ok.", i, graph.size());
    }

    private void addAndOk(Item i, String failMessage) {
	try {
	    graph.add(i);
	} catch(GraphException e) {
	    fail(failMessage + ";GraphException:" + e.getMessage());
	}
    }

    private void addAndException(Item i, String failMessage) {
	try {
	    graph.add(i);
	    fail(failMessage);
	} catch (GraphException e) {
	    assertTrue(true);
	}
    }

    private void addAndException(Item[] item, String tableName) {
	for(int i=0; i<item.length; i++) {
	    addAndException(item[i], "Problem: should not be able to add " +
			    tableName + "[" + i + "]: " + item[i]);
	}
    }

    private void assertContainsItem(Item items[]) {
	for(int i=0; i<items.length; i++) {
	    assertTrue("Problem: the element " + items[i] + "should exist",
		       graph.contains(items[i]));
	}
    }

    private void retrieveItems(Item items[]) {
	for(int i=0; i<items.length; i++) {
	    assertEquals("Problem: cannot retrieve the element " + items[i],
			graph.get(items[i].name()), items[i]);
	}
    }

    private void addEdgesAndOk(Edge[] edges) {
	for (int i=0; i<edges.length; i++) {
	    try {
		if (i%2 == 0) {
		    graph.addEdge(edges[i]);
		} else {
		    graph.addEdge(edges[i].start, edges[i].end);
		}
	    } catch (CycleException e) {
		fail("We test the dependancy graph, a CycleException should not arise:" + 
		     e.getMessage());
	    }
	}
    }

    private void assertContainsEdges(Edge[] edges) {
	String m = "The graph should contain the edge: ";
	for (int i=0; i<edges.length; i++) {
	    if (i%2 == 0) {
		assertTrue(m + edges[i], graph.containsEdge(edges[i].start, edges[i].end));
	    } else {
		assertTrue(m + edges[i], graph.containsEdge(edges[i]));
	    }
	}
    }

    
    
}
