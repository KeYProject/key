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

import java.util.LinkedList;

import de.uka.ilkd.asmkey.util.graph.DependancyGraph.IteratorOfVertexData;
import de.uka.ilkd.asmkey.util.graph.DependancyGraph.VertexData;

/**
 * this class implements depth-first traversal of a tree.
 * by overriding the methods.... one can "do" something
 * out of the traversal.
 */
public abstract class BreadthFirstTraversal extends GraphTraversal {

    public BreadthFirstTraversal(DependancyGraph graph) {
	super(graph);
    }

    protected void initWaitingSet() {
	this.waiting = new VertexQueue();
    }

    private class VertexQueue implements WaitingSet {

	LinkedList queue;
	
	public VertexQueue() {
	    queue = new LinkedList();
	}

	public boolean hasNext() {
	    return !queue.isEmpty();
	}

	public VertexData next() {
	    return (VertexData) queue.removeFirst();
	}

	public void put(VertexData vertex) {
	    queue.addLast(vertex);
	}
	
	public void put(IteratorOfVertexData vertices) {
	    while(vertices.hasNext()) {
		queue.addLast(vertices.next());
	    }
	}

    }

}
