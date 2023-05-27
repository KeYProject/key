package de.uka.ilkd.key.proof.mgt;

import javax.swing.tree.MutableTreeNode;
import javax.swing.tree.TreeNode;

import de.uka.ilkd.key.proof.Proof;

public interface TaskTreeNode extends MutableTreeNode {

    TaskTreeNode[] NO_CHILDREN = new TaskTreeNode[0];

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
