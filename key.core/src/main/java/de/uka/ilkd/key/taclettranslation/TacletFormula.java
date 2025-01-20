/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.taclettranslation;

import java.util.Collection;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.rule.Taclet;

/**
 * Represents the formula of a taclet.<br>
 * It provides methods to get the formula and its corresponding taclet.<br>
 * The setting of the formula and the taclet is dedicated to the constructor of the implementing
 * class. This ensures that the relationship between both is not changed afterwards.
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
     * @return the formula of the instance if the taclet is translatable otherwise
     *         <code>null</code>. If the translation of the taclet consists of several
     *         instantiations (e.g. the taclet has some generic sorts) the returned term is a
     *         conjunction of these instantiations.
     */
    Term getFormula(TermServices services);

    /**
     * @return if the taclet can not be translated the reason why. Otherwise a empty string.
     */
    String getStatus();


    /**
     * It can be that a taclet is translated into several formulas, i.e. in the case that the
     * generics are instantiated. This method returns the set of resulting formulas.
     */
    Collection<Term> getInstantiations();

}
