/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof.proofevent;

import de.uka.ilkd.key.logic.PosInOccurrence;


/**
 * Information about a formula that has been added or removed from a node
 */
public abstract class NodeChangeARFormula implements NodeChange {

    final PosInOccurrence pos;

    public NodeChangeARFormula(PosInOccurrence p_pos) {
        pos = p_pos;
    }

    /**
     * @return the position of the formula
     */
    @Override
    public PosInOccurrence getPos() {
        return pos;
    }

}
