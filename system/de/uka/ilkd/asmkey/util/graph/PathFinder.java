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
import java.util.NoSuchElementException;

import de.uka.ilkd.asmkey.util.graph.DependancyGraph.VertexData;
import de.uka.ilkd.key.logic.Named;

/**
 * this class implement the algorithm to find path
 * using depth-first method.
 */
public class PathFinder extends DepthFirstTraversal {

    private LinkedList path;
    private Named start;
    private Named end;

    public PathFinder(DependancyGraph graph) {
	super(graph);
	this.path = null;
	this.start = null;
	this.end = null;
    }

    private LinkedList findPathAsLinkedList(Named start, Named end) {
    
	assert start!=null && end!=null:"The start and end point may not be null.";
	reset(start, end);

	traverse(graph.getVertexData(start));
	if (wasStopped()) {
	    return path;
	} else {
	    return null;
	}
    }

    public Path findPath(Named start, Named end) {
	LinkedList list = findPathAsLinkedList(start, end);
	if(list==null) {
	    return null;
	} else {
	    list.add(end);
	    return new Path(list);
	}
    }

    /**
     * determines if there is a path between start
     * and end, but does not construct a Path object
     * @see #getComputedPath(Named start, Named end)
     */
    public boolean containsPath(Named start, Named end) {
	LinkedList list = findPathAsLinkedList(start, end);
	return (list==null)?false:true;
    }

    /** to get the path after the computation
     * WARNING returns nothing meanigfull if the
     * computation has not been done before!
     */
    Path getComputedPath(Named start, Named end) {
	LinkedList list = this.path;
	assert (start==this.start)&&(end==this.end);

	if (this.path==null) {
	    return null;
	} else {
	    list.add(end);
	    return new Path(list);
	}
    }

    public void reset(Named start, Named end) {
	reset();
	this.path = new LinkedList();
	this.start = start;
	this.end = end;
    }

    protected boolean visit(VertexData vertex) {
	try {
	    Named previous = (Named) path.getLast();
	    while (!graph.containsEdge(previous, vertex.vertex)) {
		path.removeLast();
		previous = (Named) path.getLast();
	    }
	    path.add(vertex.vertex);
	} catch (NoSuchElementException e) {
	    path.add(vertex.vertex);
	}
	return false;
    }
    
    protected boolean visitEdge(VertexData start, VertexData end) {
	if (end.name().equals(this.end.name())) {
	    return true;
	} else {
	    return false;
	}
    }

}
