// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
package de.uka.ilkd.key.smt;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.rule.Taclet;

/** 
 * A instance of <code>TacletTranslator</code> translates a single taclet to a formula.
 */

public interface TacletTranslator {
    /**Empty string that is used to indicate that a taclet can be translated. */
    public static final String TRANSLATABLE = "";
    /**
     * Translates a taclet to a formula.
     * @param t taclet to be translated
     * @return formula which expresses the meaning of the taclet.
     */
    public Term translate(Taclet t);
    
    /**
     * Checks wether the given taclet can be translated by the translator.
     * @param t taclet to be checked.
     * @return <code>TRANSLATABLE</code> if the given taclet <code>t</code> can be translated by the translator, otherwise a non empty string containing a reason.     *   */
    public String check(Taclet t);
    
     
    
  
    
}
