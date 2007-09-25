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

import de.uka.ilkd.key.logic.HashMapFromNameToNamed;
import de.uka.ilkd.key.logic.IteratorOfNamed;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Named;


/**
 * This class implements a directed acyclic graph used
 * many times in asmkey to hold dependancy graphs of
 * lemmas, named rules, units, etc...
 *
 * any classes implementing the Name interface may
 * be used as vertex.
 */
public class DependancyGraph {

    /**
     * This class contains the list-adjacency structure
     * for each vertex under the form of HashSet.
     */
    class VertexData implements Named {
	
	HashMapFromNameToNamed children;
	Named vertex;
	int incomingEdges;
	
	public VertexData(Named vertex) {
	    this.vertex = vertex;
	    this.children = new HashMapFromNameToNamed();
	    incomingEdges = 0;
	}
	
	public Name name() {
	    return vertex.name();
	}

	public void add(VertexData vertex) {
	    vertex.incrementIncomingEgdes();
	    children.put(vertex.name(), vertex);
	}
	
	public boolean contains(Named vertex) {
	    return children.containsKey(vertex.name());
	}

	public void incrementIncomingEgdes() {
	    incomingEdges++;
	}
	
	public IteratorOfVertexData children() {
	    return new VertexDataIterator(children.values());
	}

    }

    /**
     * iterator interface with included casting.
     */
    interface IteratorOfVertexData {	
	DependancyGraph.VertexData next();
	boolean hasNext();
    }

    /** This Set contains the actual
     * list of vertices contained in the graph.
     */
    private HashMapFromNameToNamed vertices;

    /**
     * computing paths is very usual operation
     * we create a PathFinder object for the
     * graph.
     */
    protected PathFinder pathFinder;
    
    public DependancyGraph() {
	vertices = new HashMapFromNameToNamed();
	pathFinder = new PathFinder(this);
    }
    
    /**
     * Add a vertex to the graph.
     * @param vertex the named object to be added
     * @throws GraphException if one attempts to add an object with the same name
     *                        as another object already contained in the graph.
     */
    public void add(Named vertex) throws GraphException {
	if (vertices.containsKey(vertex.name())) {
	    throw new GraphException
		("The graph already contains an element named: " + vertex.name() + ".");
	} else {
	    vertices.put(vertex.name(), new VertexData(vertex));
	}
    }

    /**
     * to remove a vertex from the graph, if present
     * @param vertex the vertex to be removed
     * @returns the vertex removed, if was present
     * @see #removeVertex(Name name)
     */
    public Named remove(Named vertex) {
	return remove(vertex.name());
    }

    /**
     * to remove the vertex that carries this name, if present
     * @param name the name of the vertex to be removed
     * @returns the vertex removed, if was present
     * @see #removeVertex(Named vertex)
     */
    public Named remove(Name name) {
	return getVertexFromVertexData(vertices.remove(name));
	
    }

    /**
     * to retrieve a vertex from its name
     */
    public Named get(Name name) {
	return getVertexFromVertexData(vertices.get(name));
    }

    /**
     * to test wether a vertex is in the graph or not
     * @see #contains(Name name)
     */
    public boolean contains(Named vertex) {
	return contains(vertex.name());
    }

    /**
     * to test if a vertex named by this name is in the graph or not
     * @see #contains(Named vertex)
     */
    public boolean contains(Name name) {
	return vertices.containsKey(name);
    }

    /** 
     * for a vertex. get the number of incoming edges,
     * -1 otherwise.
     */
    public int incomingEdges(Name name) {
	return getIncomingEdgesFromVertexData(vertices.get(name));
    }

    /**
     * @return the number of vertices in the graph
     */
    public int size() {
	return vertices.size();
    }

    /**
     * helper function to get vertex data
     */
    VertexData getVertexData(Named vertex) {
	
	return (VertexData) vertices.get(vertex.name());
    }

    /**
     * To add an directed edge between two vertices
     * if the vertices are not present, they are added
     * to the graph, if possible.
     *
     * this method does not throw CycleException, but 
     * derived methods may.
     *
     * @param start the start vertex of the edge
     * @param end the end vertex of the edge
     * @see #addVertex(Named vertex)
     * @see AcyclicDependancyGraph#addEdge(Named start, Named end)
     */
    public void addEdge(Named start, Named end) throws CycleException {
	try {
	    if (!contains(start)) { add(start); }
	    if (!contains(end)) { add(end); }
	} catch(GraphException e) {
	    /*
	     * This should never happen, as if the map
	     * do not contains one or the other, they
	     * must be able to add it.
	     * in case of problems (bug in the HashMap??),
	     * we throw a RuntimeException.
	     */
	    throw new RuntimeException("A FATAL error has occured in the DependancyGraph class: "
				       + "in addEdge: there was an error adding vertices.");
	}
	VertexData data = getVertexData(start);
	data.add(getVertexData(end));
    }

    /**
     * To add an edge from an Edge instance
     * @see #addEdge(Named start, Named end)
     */
    public void addEdge(Edge e) throws CycleException {
	addEdge(e.start, e.end);
    }

    /**
     * To check if an edge exists
     */
    public boolean containsEdge(Named start, Named end) {
	VertexData data = getVertexData(start);
	
	if (data == null) {
	    return false;
	} else {
	    return data.contains(end);
	}
    }

    /** 
     * check if an edge exists from an Edge instance
     * @see #containsEdge(Named start, Named end)
     */
    public boolean containsEdge(Edge e) { 
	return containsEdge(e.start, e.end);
    }


    /**
     * @return a path between start and end, if its exists; null, otherwise.
     */
    public Path getPath(Named start, Named end) {
	return pathFinder.findPath(start, end);
    }
    
    /**
     * @return a cycle for the vertex, if its exists; null, otherwise.
     */
    public Path getCycle(Named vertex) {
	return getPath(vertex, vertex);
    }

    /**
     * test if there is a path from start to end.
     */
    public boolean containsPath(Named start, Named end) {
	return pathFinder.containsPath(start, end);
    }

    /**
     * test if there is a cycle from start to end.
     */
    public boolean containsCycle(Named vertex) {
	return containsPath(vertex, vertex);
    }

    /** To iterate through the vertices
     */
    public IteratorOfNamed vertices() {
	return new VertexIterator(vertices.values());
    }

    /** To iterate through the vertices as
     * VertexData
     */
    IteratorOfVertexData verticesAsVertexData() {
	return new VertexDataIterator(vertices.values());
    }


    /** to get an iterator of the vertices */
    private class VertexIterator implements IteratorOfNamed {
	private IteratorOfNamed it;
	
	public VertexIterator(IteratorOfNamed it) {
	    this.it = it;
	}
	
	public Named next() {
	    return getVertexFromVertexData(it.next());
	}
	
	public boolean hasNext() {
	    return it.hasNext();
	}
    }
    
    /** to get an iterater of the vertices as VertexData
     */
    private class VertexDataIterator implements IteratorOfVertexData {
	IteratorOfNamed it;
	
	public VertexDataIterator(IteratorOfNamed it) {
	    this.it = it;
	}
	
	public VertexData next() {
	    return (VertexData) it.next();
	}
	
	public boolean hasNext() {
	    return it.hasNext();
	}
    }
    
    /* --- static part --- */
    
    /**
     * helper method to retrieve the vertex of
     * a vertexData or null if the vertexData is null
     */
    static final Named getVertexFromVertexData(Named vertexData) {
	if (vertexData == null) {
	    return null;
	} else {
	    return ((VertexData) vertexData).vertex;
	}
    }

    /**
     * helper function to retrive incomingEdges info
     * of a vertexData or -1 if the vertexData is null;
     */
    static final int getIncomingEdgesFromVertexData(Named vertexData) {
	if (vertexData == null) {
	    return -1;
	} else {
	    return ((VertexData) vertexData).incomingEdges;
	}
    }

}


