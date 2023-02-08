/* This file is part of KeY - https://key-project.org
 * KeY is licensed by the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0 */
package de.uka.ilkd.key.proof.mgt;

import javax.swing.tree.MutableTreeNode;
import javax.swing.tree.TreeNode;

import de.uka.ilkd.key.proof.Proof;

public interface TaskTreeNode extends MutableTreeNode {

    public static final TaskTreeNode[] NO_CHILDREN = new TaskTreeNode[0];

    ProofEnvironment getProofEnv();

    String shortDescr();

    Proof proof();

    Proof[] allProofs();

    void insertNode(TaskTreeModel model, MutableTreeNode parent);

    TreeNode[] getPath();

    ProofStatus getStatus();

    void decoupleFromEnv();

    TaskTreeNode[] getChildren();
}
