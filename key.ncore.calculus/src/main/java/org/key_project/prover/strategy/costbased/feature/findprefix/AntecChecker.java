/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.prover.strategy.costbased.feature.findprefix;

import org.key_project.prover.sequent.PosInOccurrence;

/// Checks, whether the position in occurrence is in the antecedent.
///
/// @author christoph
public class AntecChecker implements Checker {
    @Override
    public boolean check(PosInOccurrence pio) {
        return pio.isInAntec();
    }
}
