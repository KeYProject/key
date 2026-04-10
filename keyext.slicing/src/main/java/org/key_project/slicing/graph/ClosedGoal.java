/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.slicing.graph;

import de.uka.ilkd.key.proof.BranchLocation;

/**
 * Graph node that represents a closed goal.
 *
 * @author Arne Keller
 */
public class ClosedGoal extends GraphNode {
    /**
     * The serial number of the corresponding node in the proof tree.
     *
     * @see de.uka.ilkd.key.proof.Node#serialNr()
     */
    public final int serialNr;

    /**
     * Construct a new closed goal node.
     *
     * @param serialNr serial number of the proof node
     * @param branchLocation branch that was closed
     */
    public ClosedGoal(int serialNr, BranchLocation branchLocation) {
        super(branchLocation);
        this.serialNr = serialNr;
    }

    @Override
    public GraphNode popLastBranchID() {
        return new ClosedGoal(serialNr, branchLocation.removeLast());
    }

    @Override
    public String toString(boolean abbreviated, boolean omitBranch) {
        return "closed goal " + serialNr;
    }
}
