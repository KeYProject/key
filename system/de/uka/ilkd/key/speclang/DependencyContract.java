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
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.ParsableVariable;


public interface DependencyContract extends SpecificationElement {
        
    /**
     * Returns the name of the contract
     */
    public String getName();
    
    /**
     * Returns the KeYJavaType representing the class/interface to which the 
     * contract belongs.
     */
    public KeYJavaType getKJT();
    
    /**
     * Returns the observer symbol whose dependencies the contract is about 
     */
    public Operator getObserver();
    
    /**
     * The set-typed term describing the dependencies.
     */
    public Term getDependencies(ParsableVariable selfVar, Services services);
}
