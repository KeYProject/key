// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.logic;

/**
 * A Name object is created to represent the name of an object which usually
 * implements the interface {@link Named}.
 * 
 * <p>
 * It wraps a string object. To save memory and to speed up equality checks, the
 * wrapped strings are stored in their {@linkplain String#intern() interned}
 * representation.
 */
public class Name implements Comparable<Name> {

    private static final String NONAME = "_noname_";

    private final /*@Interned*/ String nameString;
    
    /**
     * creates a name object
     */
    public Name(String n) {
	nameString = (n == null ? NONAME : n).intern();
    }

    @Override
    public String toString() {
	return nameString;
    }

    @Override
    public boolean equals(Object o) {
	if (!(o instanceof Name)) {
	    return false;
	}
	// since ALL nameStrings are interned, equality can be safely reduced to
	// identity in THIS case:
	return nameString == ((Name) o).nameString;
    }

    @Override
    public int compareTo(Name o) {
	return nameString.compareTo(o.nameString);
    }
    
    @Override
    public int hashCode() {
	return nameString.hashCode();
    }

}