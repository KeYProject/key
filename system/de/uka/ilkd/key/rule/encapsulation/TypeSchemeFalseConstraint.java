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

import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.collection.ImmutableSet;


class TypeSchemeFalseConstraint implements TypeSchemeConstraint {
    public boolean evaluate() {
        return false;
    }

        
    public ImmutableSet<TypeSchemeVariable> getFreeVars() {
        return DefaultImmutableSet.<TypeSchemeVariable>nil();
    }
    
    
    public String toString() {
        return "FALSE";
    }
}
