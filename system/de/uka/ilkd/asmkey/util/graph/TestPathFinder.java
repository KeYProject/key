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
import de.uka.ilkd.asmkey.util.graph.GraphUtil.SedgewickGraph;

/**
 * To test the path finder, we use the graph
 * of sedgewick "algorithm in c", p 472 and
 * use the given Transitive closure, p. 476
 * and check all path/non path.
 * we check also the cycle if i==j
 */
public class TestPathFinder extends TestCase {

    private DependancyGraph graph;
    private Item[] items;
    private boolean[][] closure;
    private Path path;

    public void setUp() throws GraphException, CycleException {
	SedgewickGraph sed = GraphUtil.getSedgewickGraph();

	graph = sed.graph;
	items = sed.items;
	closure = sed.closure;
    }

    public void testPathFinder() {
	for(int i=0; i<closure.length; i++) {
	    for(int j=0; j<closure[i].length; j++) {
		if(closure[i][j]) {
		    assertTrue("There should be a path from " + items[i] +
			       " to " + items[j],
			       graph.containsPath(items[i], items[j]));
		} else {
		    path = graph.getPath(items[i], items[j]);
		    assertTrue("There should be no path from " + items[i] + " to " +
			       items[j] + "; the path is " +
			       ((path==null)?"":path.toString()),
			       path==null);
		}
	    }
	}
    }

}
