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

import de.uka.ilkd.key.logic.Named;

/**
 * This class extends the DependancyGraph class to make it implement
 * an acyclic graph.
 */
public class AcyclicDependancyGraph extends DependancyGraph {

    public AcyclicDependancyGraph() {
	super();
    }

    /**
     * We override this method to add the cyclicity test.
     * @param start the start vertex of the (directed) edge
     * @param end the end vertex of the edge
     * @throws CycleException if adding this edge would create a cycle
     *                        in the graph.
     */
    public void addEdge(Named start, Named end) throws CycleException {
	if (!contains(start) || !contains(end)) {
	    /* if one or both vertices are not present in the graph.
	     * then no cycle can appear when adding them and adding
	     * the edge beetween them.
	     */
	    super.addEdge(start, end);
	} else {
	    if (start == end) {
		throw new CycleException("CycleException: a edge on self creates a cycle: " +
					 start);

	    } else if (containsEdge(end, start)) {
		throw new CycleException("CycleException: there is an edge from end: " +
					 end + " and start: " + start);
	    } else if (containsPath(end, start)) {
		/* We have a path from end to start, it means
		 * that adding an edge <start, end> would cause
		 * a cycle
		 */
		throw createCycleException(start, end,
					   this.pathFinder.getComputedPath(start, end));
	    } else {
		super.addEdge(start, end);
	    }
	}
    }

    /**
     * to create a meaning full message for the CycleException 
     */
    private CycleException createCycleException(Named start, Named end, Path path) {
	return new CycleException("CycleException: the edge <" + start + ";" + end + ">" +
				  "the graph has the followng path from " + end + " to " +
				  start + ":" + path);
    }

}
