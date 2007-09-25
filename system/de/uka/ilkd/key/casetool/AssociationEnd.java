// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//


package de.uka.ilkd.key.casetool;

import de.uka.ilkd.key.logic.Name;


/**
 * An end of a UML association.
 */
public class AssociationEnd {
    private final Name roleName;
    private final Multiplicity multiplicity;
    private final ModelClass modelClass;
    
    
    public AssociationEnd(String roleName,
                          Multiplicity multiplicity,
                          ModelClass modelClass) {
        assert multiplicity != null;
        assert modelClass != null;
        
        if(roleName == null) {
            String className = modelClass.getClassName();
            roleName = className.substring(0, 0).toLowerCase() 
                       + className.substring(1);
        } 
        
        this.roleName     = new Name(roleName);
        this.multiplicity = multiplicity;
        this.modelClass   = modelClass;
    }
    
    
    public AssociationEnd(Multiplicity multiplicity,
                          ModelClass modelClass) {
        this(null, multiplicity, modelClass);
    }

    
    public Name getRoleName() {
        return roleName;
    }

    
    public Multiplicity getMultiplicity() {
        return multiplicity;
    }


    public ModelClass getModelClass() {
        return modelClass;
    }
}
