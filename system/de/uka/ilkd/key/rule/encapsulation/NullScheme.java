// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.rule.encapsulation;

import de.uka.ilkd.key.util.Debug;


class NullScheme implements TypeScheme {
    public static final NullScheme INSTANCE = new NullScheme();
    
    
    private NullScheme() {}

    
    public TypeScheme combineWith(TypeScheme ts) {
        Debug.fail("Undefined use of type scheme combinator");
        return null;
    }

    
    public boolean subSchemeOf(TypeScheme ts) {
        return (ts instanceof RepScheme
                || ts instanceof PeerScheme
                || ts instanceof ReadonlyScheme
                || ts instanceof RootScheme);
    }
    
    
    public boolean equalTo(TypeScheme ts) {
        return ts == INSTANCE;
    }

    
    public String toString() {
        return "nullS";
    }
}
