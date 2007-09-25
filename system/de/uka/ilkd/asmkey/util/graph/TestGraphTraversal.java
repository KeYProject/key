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

import java.util.*;

import junit.framework.TestCase;
import de.uka.ilkd.asmkey.util.TestUtil.Item;
import de.uka.ilkd.asmkey.util.graph.DependancyGraph.VertexData;
import de.uka.ilkd.asmkey.util.graph.GraphUtil.SedgewickGraph;
import de.uka.ilkd.key.logic.Named;

public class TestGraphTraversal extends TestCase {

    private DependancyGraph graph;
    private Item[] items;
    private int[] orders;
    private HashSet toVisit;
    private VertexOrderMap orderMap;
    private int numVisited;
    private int numEdgeVisited;

    public void setUp() throws GraphException, CycleException {
	SedgewickGraph sed = GraphUtil.getSedgewickGraph(); 
	graph = sed.graph;
	items = sed.items;
	orders = sed.orders;
	toVisit = new HashSet(Arrays.asList(items));
	orderMap = new VertexOrderMap(items);
	numVisited = 0;
	numEdgeVisited = 0;
    }

    public void testDepthFirstTraversal() {
	testTraversal(new TestDepthFirst(graph));
    }

    public void testBreadthFirstTraversal() {
	testTraversal(new TestBreadthFirst(graph));
    }

    private void testTraversal(TestGraphTraversalInterface test) {
	test.run();

	assertEquals("We should have visited " + graph.size() + " vertices",
		     graph.size(), numVisited);
	assertTrue("We should have visited all vertices: " + toVisitPrint(toVisit),
		   toVisit.isEmpty());


	for(int i=0; i<items.length; i++) {
	    assertEquals("Orders of the element " + items[i] + " do not coincide:",
			 orders[i], orderMap.get(items[i]));
	}
    }

    private String toVisitPrint(HashSet toVisit) {
	Iterator it = toVisit.iterator();
	if (it.hasNext()) {
	    String m = "[" + it.next();
	    while(it.hasNext()) {
		m += ", " + it.next();
	    }
	    m += "]";
	    return m;
	} else {
	    return "[]";
	}
    }

    private interface TestGraphTraversalInterface {
	void run();
    }

    private class TestDepthFirst extends DepthFirstTraversal
	implements TestGraphTraversalInterface {
	public TestDepthFirst(DependancyGraph graph) {
	    super(graph);
	}

	protected boolean visitEdge(VertexData start, VertexData end) {
	    numEdgeVisited++;
	    orderMap.increment(start.vertex);
	    return false;
	}

	protected boolean visit(VertexData vertex) {
	    numVisited++;
	    toVisit.remove(vertex.vertex);
	    return false;
	}

	public void run() {
	    reset();
	    traverseGraph();
	}

    }

    private class TestBreadthFirst extends BreadthFirstTraversal
	implements TestGraphTraversalInterface {
	public TestBreadthFirst(DependancyGraph graph) {
	    super(graph);
	}

	protected boolean visitEdge(VertexData start, VertexData end) {
	    numEdgeVisited++;
	    orderMap.increment(start.vertex);
	    return false;
	}

	protected boolean visit(VertexData vertex) {
	    numVisited++;
	    toVisit.remove(vertex.vertex);
	    return false;
	}

	public void run() {
	    reset();
	    traverseGraph();
	}

    }

    private class VertexOrderMap {

	private HashMap map;

	public VertexOrderMap(Named[] items) {
	    map = new HashMap(items.length);
	    for(int i=0; i<items.length; i++) {
		map.put(items[i], new Integer(0));
	    }
	}

	public int get(Named item) {
	    Integer i = (Integer) map.get(item);
	    if (i==null) {
		throw new NoSuchElementException("No int for key: " + item);
	    } else {
		return i.intValue();
	    }
	}

	public void increment(Named item) {
	    int i=get(item);

	    map.put(item, new Integer(i+1));
	}


    }
    
}
