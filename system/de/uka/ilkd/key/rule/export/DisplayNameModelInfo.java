// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.

package de.uka.ilkd.key.rule.export;

import de.uka.ilkd.key.logic.Name;



public class DisplayNameModelInfo extends AbstractTacletContainer implements Comparable<DisplayNameModelInfo> {
    private final Name name;
    
    public DisplayNameModelInfo ( String n ) {
        name = new Name ( n );
    }
    
    public DisplayNameModelInfo ( Name n ) {
        this ( n.toString () );
    }
    
    @Override
    public Name name () {
        return name;
    }
    
    @Override
    public String toString () {
        return name.toString();
    }
    
    @Override
    public int compareTo ( DisplayNameModelInfo other ) {
        return name.compareTo ( other.name );
    }
    
    @Override
    public boolean equals(Object o) {
	if(!(o instanceof DisplayNameModelInfo)) {
	    return false;
	}
	DisplayNameModelInfo dni = (DisplayNameModelInfo)o;
	return compareTo(dni) == 0;
    }
    
    @Override
    public int hashCode() {
	return name.hashCode();
    }
}
