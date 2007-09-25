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
 * tests basic features of the AcyclicDependancyGraph,
 * i.e. cyclicity tests
 */
public class TestAcyclicDependancyGraph extends TestCase {

    private AcyclicDependancyGraph graph;
    private Item[] is;

    public void testAcyclicDependancyGraph() throws GraphException {
	graph = new AcyclicDependancyGraph();

	is = new Item[11];

	for(int i=0;i<is.length; i++) {
	    is[i] = new Item("I" + i);
	    graph.add(is[i]);
	}

	addEdgeAndOk(0, 1);
	addEdgeAndOk(0, 2);
	addEdgeAndOk(1, 2);
	addEdgeAndOk(1, 3);
	addEdgeAndOk(2, 4);
	addEdgeAndOk(10, 0);
	addEdgeAndOk(8, 6);
	addEdgeAndOk(4, 5);
	addEdgeAndOk(5, 9);
	addEdgeAndOk(9, 6);
	addEdgeAndOk(7, 10);

	assertTrue(graph.containsEdge(is[0], is[1]));

	tryEdgeAndFail(0, 0);
	tryEdgeAndFail(1, 0);
	tryEdgeAndFail(3, 0);
	tryEdgeAndFail(6, 7);
	
    }

    private void addEdgeAndOk(int start, int end) throws GraphException {
	try {
	    graph.addEdge(is[start], is[end]);
	} catch (CycleException e) {
	    fail(e.toString());
	}
    }

    private void tryEdgeAndFail(int start, int end) throws GraphException {
	try {
	    graph.addEdge(is[start], is[end]);
	    fail("Adding a edge from " + is[start] + " to " + is[end] +
		 " should fail with a CycleException.");
	} catch (CycleException e) {
	    assertTrue(true);
	}
    }
}
