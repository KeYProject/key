/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof.mgt;

import javax.swing.tree.DefaultMutableTreeNode;
import javax.swing.tree.MutableTreeNode;

import de.uka.ilkd.key.proof.Proof;

public class EnvNode extends DefaultMutableTreeNode implements TaskTreeNode {

    /**
     *
     */
    private static final long serialVersionUID = 5739765420005738444L;
    private final ProofEnvironment env;

    public EnvNode(ProofEnvironment e) {
        super(e);
        env = e;
    }

    public String shortDescr() {
        return env.description();
    }

    public String toString() {
        return shortDescr();
    }

    public ProofEnvironment getProofEnv() {
        return env;
    }

    public Proof proof() {
        return getChildCount() > 0 ? ((TaskTreeNode) getChildAt(0)).proof() : null;
    }

    public Proof[] allProofs() {
        return new Proof[0];
    }


    public void insertNode(TaskTreeModel model, MutableTreeNode parentNode) {
        model.insertNodeInto(this, parentNode, model.getChildCount(parentNode));
    }

    public ProofStatus getStatus() {
        return null;
    }

    public void decoupleFromEnv() {
        // do nothing
    }

    @Override
    public TaskTreeNode[] getChildren() {
        return NO_CHILDREN;
    }

}
