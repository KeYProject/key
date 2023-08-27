/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.feature.findprefix;

import de.uka.ilkd.key.logic.PosInOccurrence;


/**
 * Interface for prefix checkers. Each checker is called on initialisation, on every operator of the
 * prefix starting with the outermost operator and for getting the result.
 *
 * @author christoph
 */
interface Checker {

    /**
     * Called to get the result of the prefix check.
     *
     * @param pio the initial position of occurrence
     */
    boolean check(PosInOccurrence pio);
}
