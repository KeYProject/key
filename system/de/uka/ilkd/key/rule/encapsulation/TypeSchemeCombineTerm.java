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


class TypeSchemeCombineTerm implements TypeSchemeTerm {
    private TypeSchemeTerm subTerm1, subTerm2;
    
    
    public TypeSchemeCombineTerm(TypeSchemeTerm subTerm1, 
                                 TypeSchemeTerm subTerm2) {
        this.subTerm1 = subTerm1;
        this.subTerm2 = subTerm2;
    }

    
    public TypeSchemeUnion evaluate() {
        return subTerm1.evaluate().combineWith(subTerm2.evaluate());
    }
    
    
    public SetOfTypeSchemeVariable getFreeVars() {
        return subTerm1.getFreeVars().union(subTerm2.getFreeVars());
    }
    
    
    public String toString() {
        return subTerm1 + " * " + subTerm2;
    }
}
