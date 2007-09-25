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

import de.uka.ilkd.key.logic.IteratorOfNamed;
import de.uka.ilkd.key.logic.Named;

/**
 * An edge is simply a ordered pair of vertex
 */
public class Edge {
    public Named start;
    public Named end;

    public Edge() {

    }

    public Edge(Named start, Named end) {
	this.start = start;
	this.end = end;
    }

    public Edge(Edge e) {
	this.start = e.start;
	this.end = e.end;
    }
    
    public String toString() {
	return "[" + start.name() + "]->[" + end.name() + "]";
    }

    
    /* --- static part --- */

    public static IteratorOfNamed endsIterator(IteratorOfEdge it) {
	return new EndsIterator (it);
    }


    private static class EndsIterator implements IteratorOfNamed {
	IteratorOfEdge it;

	public EndsIterator(IteratorOfEdge it) {
	    this.it = it;
	}

	public Named next() {
	    return it.next().end;
	}

	public boolean hasNext() {
	    return it.hasNext();
	}
    }

    
}
