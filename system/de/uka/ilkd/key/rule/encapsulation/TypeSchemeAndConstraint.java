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


class TypeSchemeAndConstraint implements TypeSchemeConstraint {
    private ListOfTypeSchemeConstraint constraints;
    
    
    public TypeSchemeAndConstraint(ListOfTypeSchemeConstraint constraints) {
        this.constraints = constraints;
    }
    

    public boolean evaluate() {
        IteratorOfTypeSchemeConstraint it = constraints.iterator();
        while(it.hasNext()) { 
            if(!it.next().evaluate()) {
                return false;
            }
        }
        
        return true;
    }

        
    public SetOfTypeSchemeVariable getFreeVars() {
        SetOfTypeSchemeVariable result 
                        = SetAsListOfTypeSchemeVariable.EMPTY_SET;
        
        IteratorOfTypeSchemeConstraint it = constraints.iterator();
        while(it.hasNext()) {
             result = result.union(it.next().getFreeVars());
        }
        
        return result;
    }
    
    
    public String toString() {
        String result = "and(";
        
        IteratorOfTypeSchemeConstraint it = constraints.iterator();
        while(it.hasNext()) {
            result += it.next() + ", ";
        }
        
        if(constraints.size() > 0) {
            result = result.substring(0, result.length() - 1);
        }
        
        result += ")";
        
        return result;
    }
}
