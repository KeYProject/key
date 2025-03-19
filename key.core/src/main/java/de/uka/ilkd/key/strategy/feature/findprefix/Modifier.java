/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.feature.findprefix;

import de.uka.ilkd.key.logic.PosInOccurrence;


/**
 * Interface for position modifiers. A position modifier is a function which gets a position and
 * delivers a (new) position as result.
 *
 * @author christoph
 */
interface Modifier {
    /**
     * Function which delivers a new position based on pos.
     *
     * @param pos the position to be modified
     * @return the (new) position
     */
    PosInOccurrence modifyPosistion(PosInOccurrence pos);
}
