/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.proof.proofevent;

import org.key_project.prover.sequent.PosInOccurrence;

/** Information about one modification of one node */
public interface NodeChange {

    /**
     * provides position information about the change
     *
     * @return position of change
     */
    PosInOccurrence getPos();

}
