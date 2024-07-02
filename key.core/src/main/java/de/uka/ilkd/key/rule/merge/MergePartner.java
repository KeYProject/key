// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2017 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.rule.merge;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;

/**
 * A {@link MergePartner} consists of a {@link Goal} and a
 * {@link PosInOccurrence}; the {@link PosInOccurrence} part indicates the
 * portion of the sequent in the {@link Goal} which represents the symbolic
 * state-program counter part.
 *
 * @author Dominic Scheurer
 */
public class MergePartner {
    private Goal goal;
    private PosInOccurrence pio;

    public MergePartner(Goal goal, PosInOccurrence pio) {
        this.goal = goal;
        this.pio = pio;
    }

    /**
     * @return The merge partner goal.
     */
    public Goal getGoal() {
        return goal;
    }

    public void setGoal(Goal goal) {
        this.goal = goal;
    }

    /**
     * @return The {@link PosInOccurrence} representing the symbolic
     *         state-program counter part of the {@link MergePartner}.
     */
    public PosInOccurrence getPio() {
        return pio;
    }

    public void setPio(PosInOccurrence pio) {
        this.pio = pio;
    }
}
