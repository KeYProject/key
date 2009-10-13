// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
package de.uka.ilkd.key.smt.taclettranslation;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.rule.Taclet;

/** 
 * A instance of <code>TacletTranslator</code> translates a single taclet to a formula.
 */

public interface TacletTranslator {

    /**
     * Translates a taclet to a formula.
     * @param t taclet to be translated
     * @return formula which expresses the meaning of the taclet.
     * @throw  IllegalTacletException if the taclet is not translatable.
     */
    public Term translate(Taclet t) throws IllegalTacletException;
    
   
    
     
    
  
    
}
