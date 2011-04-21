// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2011 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.smt.taclettranslation;

import java.util.Collection;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.rule.Taclet;

/**
 * Represents the formula of a taclet.<br>
 * It provides methods to get the formula and its corresponding taclet.<br>
 * The setting of the formula and the taclet is dedicated to the constructor of
 * the implementing class. This ensures that the relationship between both is
 * not changed afterwards.
 */
public interface TacletFormula {

    /**
     * 
     * @return the taclet of the instance.
     */
    Taclet getTaclet();

    /**
     * 
     * @return the formula of the instance if the taclet is translatable
     *         otherwise <code>null</code>. If the translation of the taclet
     *         consists of several instantiations (e.g. the taclet has some
     *         generic sorts) the returned term is a conjunction of these 
     *         instantiations.
     */
    Term getFormula();

    /**
     * @return if the taclet can not be translated the reason why. Otherwise a
     *         empty string.
     */
    String getStatus();
    


    Collection<Term> getInstantiations();
    
}
