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


class TypeSchemeVariable implements TypeSchemeTerm {
    private final String name;
    private final TypeSchemeUnion defaultValue;
    private TypeSchemeUnion value;
    
    
    public TypeSchemeVariable(String name, TypeSchemeUnion defaultValue) {
        this.name = name;
        this.defaultValue = defaultValue;
        assignDefaultValue();
    }
    
    
    public TypeSchemeUnion getDefaultValue() {
        return defaultValue;
    }
    
    
    public SetOfTypeScheme getValueRange() {
        return defaultValue.getPossibilities();
    }


    public void assignDefaultValue() {
        value = defaultValue;
    }
    
    
    public void assignValue(TypeSchemeUnion value) {
        this.value = value;
    }
    
    
    public void assignValue(TypeScheme scheme) {
        assignValue(new TypeSchemeUnion(scheme));
    }


    public boolean valueIsExact() {
        return value.isExact();
    }
        
    
    public TypeSchemeUnion evaluate() {
        return value;
    }
    
    
    public SetOfTypeSchemeVariable getFreeVars() {
        return SetAsListOfTypeSchemeVariable.EMPTY_SET.add(this);
    }
    
    
    public String toString() {
        return name;
    }
}
