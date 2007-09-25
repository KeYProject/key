// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.asmkey.unit;

import de.uka.ilkd.asmkey.util.graph.AcyclicDependancyGraph;
import de.uka.ilkd.asmkey.util.graph.CycleException;
import de.uka.ilkd.asmkey.util.graph.GraphException;
import de.uka.ilkd.asmkey.util.graph.TopologicalOrder;
import de.uka.ilkd.key.logic.IteratorOfNamed;
import de.uka.ilkd.key.logic.Name;

/**
 * This graph is created by the UnitManager and represent the
 * dependancy graph of the different units; its vertex are Unit.
 */
public class UnitGraph {
    
    private AcyclicDependancyGraph graph;
    private TopologicalOrder order;

    public UnitGraph() {
	graph = new AcyclicDependancyGraph();
	order = new TopologicalOrder(graph);
    }

    public void add(Unit unit) throws GraphException {
	unit.setGraph(this);
	graph.add(unit);
    }

    public boolean contains(Unit unit) {
	return graph.contains(unit);
    }

    public boolean contains(Name name) {
	return graph.contains(name);
    }

    public void addEdge(Unit start, Unit end) throws CycleException {
	graph.addEdge(start, end);
    }
    
    public boolean containsEdge(Unit start, Unit end) {
	return graph.containsEdge(start, end);
    }
    
    public boolean containsPath(Unit start, Unit end) {
	return graph.containsPath(start, end);
    }

    public Unit get(Name name) {
	return (Unit) graph.get(name);
    }

    public int size() {
	return graph.size();
    }

    public IteratorOfUnit iterator() {
	return new UnitIterator(graph.vertices());
    }

    public IteratorOfUnit orderedIterator() {
	return new UnitIterator(order.reverseTopologicalOrder());
    }

 //    public IteratorOfUnit orderedIterator(Unit unit) {
// 	return new UnitIterator(order.reverseTopologicalOrder(unit));
//     }

//     public IteratorOfUnit reverseListForLoading() {
// 	return new UnitIterator(order.topologicalOrder());
//     }

//     public IteratorOfUnit reverseListForLoading(Unit unit) {
// 	return new UnitIterator(order.topologicalOrder(unit));
//     }

    private class UnitIterator implements IteratorOfUnit {

	IteratorOfNamed it;
	
	public UnitIterator(IteratorOfNamed it) {
	    this.it = it;
	}

	public Unit next() {
	    return (Unit) it.next();
	}

	public boolean hasNext() {
	    return it.hasNext();
	}
	
    }

}
