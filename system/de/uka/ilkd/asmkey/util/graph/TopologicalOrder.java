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

import java.util.HashMap;
import java.util.LinkedList;
import java.util.ListIterator;

import de.uka.ilkd.asmkey.util.CollectionUtil;
import de.uka.ilkd.asmkey.util.graph.DependancyGraph.VertexData;
import de.uka.ilkd.key.logic.IteratorOfNamed;
import de.uka.ilkd.key.logic.Named;

/**
 * This method computes a list in topological order (or inverse topological order)
 * of a dag by using the DepthFirstTraversal method.
 * the meaning of an edge a->b is that a in greater than b.
 */
public class TopologicalOrder extends DepthFirstTraversal {
    
    LinkedList list;
    ListIterator it;
    HashMap map;

    public TopologicalOrder(AcyclicDependancyGraph graph) {
	super(graph);
    }

    public void reset() {
	super.reset();
	this.list = new LinkedList();
	this.it = list.listIterator();
	this.map = new HashMap(graph.size());
	IteratorOfNamed it = graph.vertices();
	while (it.hasNext()) {
	    Named item = it.next();
	    int in = graph.incomingEdges(item.name());
	    map.put(item.name(), new Integer(in));
	    if (in == 0) {
		this.waiting.put(this.graph.getVertexData(item));
	    }
	}
    }

    protected boolean visit(VertexData vertex) {
	this.it.add(vertex.vertex);
	return false;
    }

    protected boolean visitEdge(VertexData start, VertexData end) {
	Integer i = (Integer) map.get(end.name());
	map.put(end.name(), new Integer(i.intValue() -1));
	return false;
    }

    /**
     * we may visit a vertex only if it is through it last
     * visited incoming edge.
     */
    protected boolean toBeVisitedNow(VertexData child) {
	return ((Integer) map.get(child.name())).intValue() == 0;
    }

    protected boolean traverseFinished(VertexData vertex) {
	this.it = this.list.listIterator();
	return false;
    }

    public IteratorOfNamed topologicalOrder() {
	return CollectionUtil.convertToIteratorOfNamed(topOrder(false));
    }

    public IteratorOfNamed reverseTopologicalOrder() {
	return new ReverseIterator(topOrder(true));
    }

    private ListIterator topOrder(boolean last) {
	reset();
	traverse();
	return list.listIterator(last?list.size():0);
    }

    private class ReverseIterator implements IteratorOfNamed {
	ListIterator it;

	public ReverseIterator(ListIterator it) {
	    this.it = it;
	}

	public Named next() {
	    return (Named) it.previous();
	}
	
	public boolean hasNext() {
	    return it.hasPrevious();
	}
    }

}
