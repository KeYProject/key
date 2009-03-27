// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//This file is part of KeY - Integrated Deductive Software Design 
//Copyright (C) 2001-2003 Universitaet Karlsruhe, Germany
//                      and Chalmers University of Technology, Sweden
//
//The KeY system is protected by the GNU General Public License.
//See LICENSE.TXT for details.
//

package de.uka.ilkd.key.rule.export;

import de.uka.ilkd.key.logic.Name;



public class DisplayNameModelInfo extends AbstractTacletContainer implements Comparable {
    private final Name name;
    
    public DisplayNameModelInfo ( String n ) {
        name = new Name ( n );
    }
    
    public DisplayNameModelInfo ( Name n ) {
        this ( n.toString () );
    }
    
    public Name name () {
        return name;
    }
    
    public String toString () {
        return name.toString();
    }
    
    public int compareTo ( Object other ) {
        return name.compareTo ( ((DisplayNameModelInfo) other).name );
    }
}
