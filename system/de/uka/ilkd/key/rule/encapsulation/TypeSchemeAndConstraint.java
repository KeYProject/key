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

import java.util.Iterator;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.collection.ImmutableSet;


class TypeSchemeAndConstraint implements TypeSchemeConstraint {
    private ImmutableList<TypeSchemeConstraint> constraints;
    
    
    public TypeSchemeAndConstraint(ImmutableList<TypeSchemeConstraint> constraints) {
        this.constraints = constraints;
    }
    

    public boolean evaluate() {
        for (TypeSchemeConstraint constraint : constraints) {
            if (!constraint.evaluate()) {
                return false;
            }
        }
        
        return true;
    }

        
    public ImmutableSet<TypeSchemeVariable> getFreeVars() {
        ImmutableSet<TypeSchemeVariable> result 
                        = DefaultImmutableSet.<TypeSchemeVariable>nil();

        for (TypeSchemeConstraint constraint : constraints) {
            result = result.union(constraint.getFreeVars());
        }
        
        return result;
    }
    
    
    public String toString() {
        String result = "and(";

        for (TypeSchemeConstraint constraint : constraints) {
            result += constraint + ", ";
        }
        
        if(constraints.size() > 0) {
            result = result.substring(0, result.length() - 1);
        }
        
        result += ")";
        
        return result;
    }
}
