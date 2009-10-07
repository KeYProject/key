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

import de.uka.ilkd.key.collection.ImmutableSet;


class TypeSchemeSubConstraint implements TypeSchemeConstraint {
    private TypeSchemeTerm term1, term2;

    
    public TypeSchemeSubConstraint(TypeSchemeTerm term1, TypeSchemeTerm term2) {
        this.term1 = term1;
        this.term2 = term2;
    }


    public boolean evaluate() {
        return term1.evaluate().subSchemeOf(term2.evaluate());
    }

        
    public ImmutableSet<TypeSchemeVariable> getFreeVars() {
        return term1.getFreeVars().union(term2.getFreeVars());
    }
    
    
    public String toString() {
        return term1 + " <= " + term2;
    }
}
