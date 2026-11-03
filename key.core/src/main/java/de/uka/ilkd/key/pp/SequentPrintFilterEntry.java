/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.pp;

import org.key_project.prover.sequent.SequentFormula;

import org.jspecify.annotations.NullMarked;


/**
 * One element of a sequent as delivered by SequentPrintFilter
 */

@NullMarked
public interface SequentPrintFilterEntry {

    /**
     * Formula to display
     */
    SequentFormula getFilteredFormula();

    /**
     * Original formula from sequent
     */
    SequentFormula getOriginalFormula();

}
