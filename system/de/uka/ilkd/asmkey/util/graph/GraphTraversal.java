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

import java.util.HashSet;

import de.uka.ilkd.asmkey.util.graph.DependancyGraph.IteratorOfVertexData;
import de.uka.ilkd.asmkey.util.graph.DependancyGraph.VertexData;

/**
 * this class implements traversal of a tree.
 * by overriding the methods .
 */
public abstract class GraphTraversal {

    public interface WaitingSet {

	boolean hasNext();

	VertexData next();

	void put(VertexData vertex);
	
	void put(IteratorOfVertexData vertices);

    }

    protected DependancyGraph graph;
    protected WaitingSet waiting;
    private VisitedSet visited;
    private boolean stop;

    public GraphTraversal(DependancyGraph graph) {
	assert graph!=null:"The DependancyGraph may not be null";
	this.graph = graph;
	this.stop = false;
	this.visited = null;
	this.waiting = null;
    }

    /**
     * to reset the internal state, for restarting a traversal.
     */
    public void reset() {
	this.stop = false;
	this.visited = new VisitedSet();
	initWaitingSet();
    }

    /**
     * concrete derived class must implement this method
     * to create an initial waitingSet();
     */
    protected abstract void initWaitingSet();

    /**
     * concrete derived class may implement this method
     * to do actual work besides the traversal.
     *
     * the original does nothing.
     */
    protected boolean visit(VertexData vertex) { return false; }

    /**
     * when the child is encountered, should we add
     * it to the waiting set or not. in some algorithm,
     * it is necessary to wait until some condition is
     * fullfiled.
     *
     * the original returns true.
     * @see TopologicalOrder
     */
    protected boolean toBeVisitedNow(VertexData vertex) {return true;}

    /**
     * concrete derived class may implement this method
     * to do actual work besides the traversal of the edge.
     * 
     * the original does nothing
     */
    protected boolean visitEdge(VertexData start, VertexData end) {
	return false;
    }

    /**
     * concrete derived class may derive this method to do some
     * work when the method traverse(vertex) has finished.
     * this means that we have finished visiting the vertices from
     * vertex has start.
     * 
     * the original does nothing.
     */
    protected boolean traverseFinished(VertexData vertex) { return false; }

    boolean wasStopped() {
	return stop;
    }

    /* we traverse all the graph.
     */
    void traverseGraph() {
	IteratorOfVertexData it = this.graph.verticesAsVertexData();
	VertexData vertex;
	while(it.hasNext()) {
	    /**
	     * if, for some reason, the algormith has
	     * stoped before, we break; otherwise, we
	     * keeps visiting.
	     */
	    if (stop) {
		break;
	    } else {
		vertex = it.next(); 
		if (!visited.contains(vertex)) {
		    traverse(vertex);
		}
	    }
	}
    }

    void traverse(VertexData startFrom) {
	/* we push the start node on the waiting list
	 * and start the traversal.
	 */
	waiting.put(startFrom);
	traverse();
	/* We have processed all the children and sub-children from
	 * startFrom, if it was not stopped, we can now register
	 * this fact. */
	if(!stop) {
	    stop = traverseFinished(startFrom);
	}
    }

    void traverse() {
	/* as long as the waiting list is not empty,
	 * we can continue 
	 */
	while(waiting.hasNext()) {
	    /* we take the first element of the waiting list */
	    VertexData element = waiting.next();
	    /* if we have already visited the element, we
	     * must skip, otherwise we visit it and
	     * its children
	     */
	    if (!visited.contains(element)) {
		/* we visit it and put it out of the visited set */
		stop = visit(element); visited.add(element);
		/* if visiting the element did not stop
		 * algorithm, we put its children on the waiting list 
		 * and we continue; otherwise, we finish the algorithm
		 */
		if(stop) {break;} 

		/* we now visit the edges that starts from element
		 * and so long the process is not stopped, we add
		 * the children to the waiting set; to be visited
		 * later.
		 */
		IteratorOfVertexData it = element.children();
		VertexData child = null;
		while (it.hasNext()) {
		    child = it.next();
		    stop = visitEdge(element, child);
		    /* if visiting the edge stopped the process, 
		     * we can break.
		     */
		    if(stop) {break;}
		    /* if the child should be visited "now", i.e. it may
		     * as from now be visited, add it to the waiting set.
		     */
		    if (toBeVisitedNow(child)) {
			waiting.put(child);
		    }
		}
	    }
	    /* we must stop if visiting an edge has stopped the traversal. */
	    if(stop) {break;}
	}
    }

    
    /**
     * the class wraps a HashSet and do the necessary casting
     */
    private class VisitedSet {
	
	private HashSet set;

	public VisitedSet() {
	    set = new HashSet();
	}

	public void add(VertexData vertex) {
	    set.add(vertex);
	}

	public boolean contains(VertexData vertex) {
	    return set.contains(vertex);
	}
	
    }
    
}
