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

import java.util.Collection;
import java.util.NoSuchElementException;

import de.uka.ilkd.key.logic.IteratorOfNamed;
import de.uka.ilkd.key.logic.ListOfNamed;
import de.uka.ilkd.key.logic.Named;

public class Path {

    private Named[] path;
    
    public Path(ListOfNamed path) {
	this(path.toArray());
    }

    public Path(Collection path) {
	this((Named[])path.toArray(new Named[path.size()])); 
    }

    public Path(Named[] path) {
	assert path.length<2:"A path consists of at least two vertices.";
	this.path = path;
    }

    public IteratorOfNamed iterator() {
	return new PathIterator(path); 
    }

    private class PathIterator implements IteratorOfNamed {

	private Named[] path;
	private int index;
	private int max_index;

	public PathIterator(Named[] path) {
	    this.path = path;
	    this.max_index = path.length;
	    this.index = 0;
	}
	
	public Named next() {
	    try {
		return path[index++];
	    } catch (IndexOutOfBoundsException e) {
		throw new NoSuchElementException();
	    }
	}

	public boolean hasNext() {
	    return index<max_index;
	}

    }

    public String toString() {
	String s = path[0].toString();
	for(int i = 1; i<path.length; i++) {
	    s += "->" + path[1];
	}
	return s;
    }

}
