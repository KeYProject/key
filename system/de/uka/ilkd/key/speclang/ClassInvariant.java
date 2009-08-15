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
import de.uka.ilkd.key.logic.op.ParsableVariable;


/**
 * A class invariant.
 */
public interface ClassInvariant {
        
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
     * Returns the invariant formula with implicit all-quantification over
     * the receiver object.
     */
    public FormulaWithAxioms getClosedInv(Services services);
    
    /**
     * Returns the invariant formula with implicit all-quantification over
     * all objects, excluding the object held by the passed variable.
     */
    public FormulaWithAxioms getClosedInvExcludingOne(
	    					ParsableVariable excludedVar, 
	                                        Services services);
    
  
    /**
     * Returns the invariant formula without implicit all-quantification over
     * the receiver object.
     */
    public FormulaWithAxioms getOpenInv(ParsableVariable selfVar, 
	      			        Services services);
    
    /**
     * Returns the invariant in pretty HTML format.
     */
    public String getHTMLText(Services services);
}
