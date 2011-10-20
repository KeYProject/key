// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2011 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.util;


public class Pair<T1, T2> {    
    public final T1 first;
    public final T2 second;

    
    public Pair(T1 first, T2 second) { 
	this.first = first;
	this.second = second;   
    }


    public String toString() { 
	return "(" + first + ", " + second + ")"; 
    }
    
    
    public boolean equals(Object o) {
	if(!(o instanceof Pair<?, ?>)) {
	    return false;
	} 
	Pair<?, ?> p = (Pair<?, ?>) o;
	return (first == null ? p.first == null : first.equals(p.first))
	       && (second == null ? p.second == null : second.equals(p.second));
    }
    
    
    public int hashCode() {
	return first.hashCode() + second.hashCode();
    }
}
