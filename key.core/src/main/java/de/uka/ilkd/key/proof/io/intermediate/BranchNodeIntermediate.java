/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.proof.io.intermediate;

import org.jspecify.annotations.NullMarked;

/**
 * Node in an intermediate proof representation modeling a branch node. This node has a title
 * (branch identifier) should have exactly one child. Only exception: An empty proof; in this case,
 * there is the only branch "dummy ID" that has no parseable children.
 *
 * @author Dominic Scheurer
 */
@NullMarked
public class BranchNodeIntermediate extends NodeIntermediate {

    /**
     * The branch title of this branch node. It is always assigned by the single constructor before
     * the node is used; the {@code null} initializer merely marks the intermediate's pre-writing
     * state and is suppressed with a scoped key.
     */
    @SuppressWarnings("nullness:assignment.type.incompatible")
    private String branchTitle = null;

    public BranchNodeIntermediate(String branchTitle) {
        this.branchTitle = branchTitle;
    }

    public String getBranchTitle() {
        return branchTitle;
    }

}
