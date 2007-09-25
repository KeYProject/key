// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.rule.encapsulation;

import de.uka.ilkd.key.util.Debug;


class ThisScheme implements TypeScheme {
    public static final ThisScheme INSTANCE = new ThisScheme();
    
    
    private ThisScheme() {}

    
    public TypeScheme combineWith(TypeScheme ts) {
        if(ts instanceof PrimitiveScheme) {
            return ts;
        } else if(ts instanceof RepScheme) {
            return ts;
        } else if(ts instanceof PeerScheme) {
            return ts;
        } else if(ts instanceof ReadonlyScheme) {
            return ts;
        } else if(ts instanceof RootScheme) {
            return ts;
        }
        
        Debug.fail("Undefined use of type scheme combinator");
        return null;
    }
    

    public boolean subSchemeOf(TypeScheme ts) {
        return (ts instanceof PeerScheme || ts instanceof ReadonlyScheme);
    }
    
    
    public boolean equalTo(TypeScheme ts) {
        return ts == INSTANCE;
    }
    
    
    public String toString() {
        return "thisS";
    }
}
