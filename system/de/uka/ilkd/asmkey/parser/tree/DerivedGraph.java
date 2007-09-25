// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.asmkey.parser.tree;

import de.uka.ilkd.asmkey.logic.DerivedFunction;
import de.uka.ilkd.asmkey.logic.IteratorOfDerivedFunction;
import de.uka.ilkd.asmkey.util.graph.CycleException;
import de.uka.ilkd.asmkey.util.graph.DependancyGraph;
import de.uka.ilkd.asmkey.util.graph.GraphException;
import de.uka.ilkd.key.logic.IteratorOfNamed;
import de.uka.ilkd.key.logic.Name;

/**
 * Graphs of this class are used during the parsing
 * of the derived symbols, to determine recursivity 
 * and other information.
 * @see DerivedFunctionParser
 */
public class DerivedGraph {

    DependancyGraph graph;
    
    public DerivedGraph() {
	this.graph = new DependancyGraph();
    }

    public void add(DerivedFunction func) throws GraphException {
	graph.add(func);
    }

    public DerivedFunction get(Name name) {
	return (DerivedFunction) graph.get(name);
    }

    public boolean contains(DerivedFunction func) {
	return graph.contains(func);
    }

    public boolean contains(Name name) {
	return graph.contains(name);
    }

    public void addEdge(DerivedFunction func1, DerivedFunction func2) {
	try {
	    graph.addEdge(func1, func2);
	} catch (CycleException e) {
	    throw new RuntimeException("MAJOR PROBLEM: this exception should never been" +
				       "throws as we use a DependancyGraph and not a " +
				       "AcyclicDependancyGraph: " + e.toString());
	}
    }

    public boolean isRecursive(DerivedFunction func) {
	return graph.containsCycle(func);
    }

    public IteratorOfDerivedFunction iterator() {
	return new Iterator(graph.vertices());
    }

    DependancyGraph graph() {
	return graph;
    }

    private class Iterator implements IteratorOfDerivedFunction {

	private IteratorOfNamed it;

	public Iterator(IteratorOfNamed it) {
	    this.it = it;
	}

	public boolean hasNext() {
	    return it.hasNext();
	}

	public DerivedFunction next() {
	    return (DerivedFunction) it.next();
	}

    }

}
