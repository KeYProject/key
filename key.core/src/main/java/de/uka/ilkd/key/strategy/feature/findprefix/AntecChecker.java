/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.feature.findprefix;

import de.uka.ilkd.key.logic.PosInOccurrence;
import org.jspecify.annotations.NonNull;

/**
 * Checks, whether the position in occurrence is in the antecedent.
 *
 * @author christoph
 */
class AntecChecker implements Checker {

    @Override
    public boolean check(@NonNull PosInOccurrence pio) {
        return pio.isInAntec();
    }

}
