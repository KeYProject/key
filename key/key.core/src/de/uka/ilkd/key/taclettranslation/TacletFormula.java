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

package de.uka.ilkd.key.taclettranslation;

import java.util.Collection;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermServices;
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
     * @param services TODO
    * @return the formula of the instance if the taclet is translatable
     *         otherwise <code>null</code>. If the translation of the taclet
     *         consists of several instantiations (e.g. the taclet has some
     *         generic sorts) the returned term is a conjunction of these 
     *         instantiations.
     */
    Term getFormula(TermServices services);

    /**
     * @return if the taclet can not be translated the reason why. Otherwise a
     *         empty string.
     */
    String getStatus();
    

    /**
     * It can be that a taclet is translated into several formulas, i.e. in the case
     * that the generics are instantiated. This method returns the set of resulting formulas. 
     */
    Collection<Term> getInstantiations();
    
}