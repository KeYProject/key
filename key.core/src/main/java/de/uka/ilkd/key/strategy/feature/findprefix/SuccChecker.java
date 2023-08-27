/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.feature.findprefix;

import de.uka.ilkd.key.logic.PosInOccurrence;

/**
 * Checks, whether the position in occurrence is in the succedent.
 *
 * @author christoph
 */
class SuccChecker implements Checker {

    @Override
    public boolean check(PosInOccurrence pio) {
        return !pio.isInAntec();
    }

}
