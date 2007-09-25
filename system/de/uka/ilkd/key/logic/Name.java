// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.logic;

/**
 * A Name object is created to represent the name of an object which
 * usually implements the interface {@link Named}.
 */
public class Name {
    
    protected final String nameString;

    private final int hashCode;

    /** 
     * creates a name object 
     * 
     * 
     */
    public Name(String n) {
        // .intern() is crucial for correct equals and performance
	nameString = ((n==null) ? "_noname_" : n).intern(); 
	hashCode = nameString.hashCode();
    }

    public String toString() {
	return nameString;
    }

    public boolean equals(Object o) {
	if (! (o instanceof Name)) {
	    return false;
	}
	return nameString.equals(((Name)o).nameString);
    }

    public int compareTo(Object o) {
	return nameString.compareTo(((Name)o).nameString);
    }

    public int hashCode() {
	return hashCode;
    }

}
