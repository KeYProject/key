/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.slicing.graph;

import de.uka.ilkd.key.proof.BranchLocation;

/**
 * Graph node used if a rule application did not use any input formulas.
 * This is required to ensure that all rule application are present in the graph.
 *
 * @author Arne Keller
 */
public class PseudoInput extends GraphNode {
    /**
     * Construct a new pseudo input node.
     */
    public PseudoInput() {
        super(BranchLocation.ROOT); // branch location of pseudo outputs does not matter
    }

    @Override
    public GraphNode popLastBranchID() {
        return this;
    }

    @Override
    public String toString(boolean abbreviated, boolean omitBranch) {
        return "pseudo input " + Integer.toHexString(hashCode());
    }
}
