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

import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.modifier.VisibilityModifier;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.util.Pair;


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
     * Returns the pairs (kjt, obs) for which there is an occurrence of
     * o.obs in the axiom, where kjt is the type of o (excluding the
     * defining occurrence of the axiom target). 
     */
    public ImmutableSet<Pair<Sort, ObserverFunction>> getUsedObservers(
	    						Services services);
    
    /**
     * The axiom as one or many taclets, where the non-defining occurrences of
     * the passed observers are replaced by their "limited" counterparts.
     */
    public ImmutableSet<Taclet> getTaclets(
	    		ImmutableSet<Pair<Sort, ObserverFunction>> toLimit,
	    		Services services);    
}
