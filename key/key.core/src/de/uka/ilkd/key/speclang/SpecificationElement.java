// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.speclang;

import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.modifier.VisibilityModifier;


/**
 * Common superinterface of all constructs created by the specification
 * language front ends and managed by SpecificationRepository.
 */
public interface SpecificationElement {
    
    /**
     * Returns the unique internal name of the specification element.
     */
    public String getName();
    
    /**
     * Returns the displayed name.
     */
    public String getDisplayName();
    
    /**
     * Returns the visibility of the invariant (null for default visibility)
     */    
    public VisibilityModifier getVisibility();
    

    /**
     * Returns the KeYJavaType representing the class/interface to which the 
     * specification element belongs.
     */
    public KeYJavaType getKJT();
}