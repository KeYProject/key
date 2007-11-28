// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.rule.encapsulation;

import de.uka.ilkd.key.util.Debug;


class RootScheme implements TypeScheme {
    public static final RootScheme INSTANCE = new RootScheme();
    
    
    private RootScheme() {}

    
    public TypeScheme combineWith(TypeScheme ts) {
        if(ts instanceof PrimitiveScheme) {
            return ts;
        } else if(ts instanceof RepScheme) {
            return ReadonlyPrimeScheme.INSTANCE;
        } else if(ts instanceof PeerScheme) {
            return RootScheme.INSTANCE;
        } else if(ts instanceof ReadonlyScheme) {
            return ts;
        } else if(ts instanceof RootScheme) {
            return ts;
        }
        
        Debug.fail("Undefined use of type scheme combinator");
        return null;
    }
    

    public boolean subSchemeOf(TypeScheme ts) {
        return (ts instanceof RootScheme || ts instanceof ReadonlyScheme);
    }
    
    
    public boolean equalTo(TypeScheme ts) {
        return ts == INSTANCE;
    }
    
    
    public String toString() {
        return "rootS";
    }
}
