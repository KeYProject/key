/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof.io.intermediate;

/**
 * Node in an intermediate proof representation modeling a branch node. This node has a title
 * (branch identifier) should have exactly one child. Only exception: An empty proof; in this case,
 * there is the only branch "dummy ID" that has no parseable children.
 *
 * @author Dominic Scheurer
 */
public class BranchNodeIntermediate extends NodeIntermediate {

    private String branchTitle = null;

    public BranchNodeIntermediate(String branchTitle) {
        this.branchTitle = branchTitle;
    }

    public String getBranchTitle() {
        return branchTitle;
    }

}
