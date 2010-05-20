// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.speclang;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.modifier.VisibilityModifier;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.ParsableVariable;


/**
 * A class invariant.
 */
public interface ClassInvariant extends SpecificationElement {
        
    /**
     * Returns the unique internal name of the invariant.
     */
    public String getName();
    
    /**
     * Returns the displayed name of the invariant.
     */
    public String getDisplayName();

    /**
     * Returns the KeYJavaType representing the class/interface to which the 
     * invariant belongs.
     */
    public KeYJavaType getKJT();
    
    /**
     * Returns the visibility of the invariant (null for default visibility)
     */
    public VisibilityModifier getVisibility();     
    
    /**
     * Returns the invariant formula without implicit all-quantification over
     * the receiver object.
     */
    public Term getInv(ParsableVariable selfVar, Services services);
    
    /**
     * Tells whether the invariant is static (i.e., does not refer to a
     * receiver object).
     */
    public boolean isStatic();
        
    /**
     * Returns another class invariant like this one, except that it refers to the 
     * passed KeYJavaType.
     */    
    public ClassInvariant setKJT(KeYJavaType kjt);
}
