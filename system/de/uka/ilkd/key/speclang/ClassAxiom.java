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
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.rule.Taclet;


public interface ClassAxiom extends SpecificationElement {
        
    /**
     * Returns the name of the axiom
     */
    public String getName();
    
    /**
     * Returns the axiomatised function symbol. 
     */
    public ObserverFunction getTarget();
    
    /**
     * Returns the KeYJavaType representing the class/interface to which the 
     * axiom belongs.
     */
    public KeYJavaType getKJT();
    
    /**
     * Returns the visibility of the invariant (null for default visibility)
     */    
    public VisibilityModifier getVisibility();
    
    /**
     * The axiom as a formula.
     */
    public Term getAxiom(Services services);
    
    /**
     * The axiom as a taclet.
     */
    public Taclet getAxiomAsTaclet(Services services);
}
