// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
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
 * 
 * <p>
 * TODO Reconsider hash caching: 
 * This implementation precalculates and caches
 * the string's hashvalue. Since {@link String#hashCode()} itself also caches
 * the value, there is no immediate need to do this here a second time.
 */
public class Name implements Comparable<Name> {

    private static final String NONAME = "_noname_";

    private final /*@Interned*/ String nameString;

    private final int hashCode;

    /**
     * creates a name object
     */
    public Name(String n) {
	nameString = (n == null ? NONAME : n).intern();
	hashCode = nameString.hashCode();
    }

    public String toString() {
	return nameString;
    }

    public boolean equals(Object o) {
	if (!(o instanceof Name)) {
	    return false;
	}
	// since ALL nameStrings are interned, equality can be safely reduced to
	// identity in THIS case:
	return nameString == ((Name) o).nameString;
    }

    public int compareTo(Name o) {
	return nameString.compareTo(o.nameString);
    }

    public int hashCode() {
	return hashCode;
    }

}
