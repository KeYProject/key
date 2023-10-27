/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof.proofevent;

import de.uka.ilkd.key.logic.PosInOccurrence;

/**
 * An instance of this class informs the listerns if a formula has been tried to add to the sequent
 */
public class NodeRedundantAddChange implements NodeChange {

    /** the PosInOccurrence of the formula that has been tried to add */
    private final PosInOccurrence pio;

    /**
     * creates an instance
     *
     * @param pio the PosInOccurrence of the formula that has been tried to add
     */
    public NodeRedundantAddChange(PosInOccurrence pio) {
        this.pio = pio;
    }

    /**
     * returns the PosInOccurrence of the formula that has been tried to add
     *
     * @return the PosInOccurrrence
     */
    @Override
    public PosInOccurrence getPos() {
        return pio;
    }

    /** toString */
    @Override
    public String toString() {
        return "Redundant formula:" + pio;
    }

}
