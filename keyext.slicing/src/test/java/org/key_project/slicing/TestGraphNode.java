/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.slicing;

import de.uka.ilkd.key.proof.BranchLocation;

import org.key_project.slicing.graph.GraphNode;

public class TestGraphNode extends GraphNode {
    TestGraphNode() {
        super(BranchLocation.ROOT);
    }

    @Override
    public GraphNode popLastBranchID() {
        return this;
    }

    @Override
    public String toString(boolean abbreviated, boolean omitBranch) {
        return toString();
    }
}
