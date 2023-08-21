/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof.mgt;

import java.util.LinkedHashMap;
import java.util.Map;
import javax.swing.tree.DefaultMutableTreeNode;
import javax.swing.tree.DefaultTreeModel;
import javax.swing.tree.MutableTreeNode;

import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofAggregate;


public class TaskTreeModel extends DefaultTreeModel {

    /**
    *
    */
    private static final long serialVersionUID = -4168248377205879699L;
    private final Map<Proof, TaskTreeNode> proofToTask = new LinkedHashMap<>();

    public TaskTreeModel() {
        super(new DefaultMutableTreeNode("Tasks"));
    }

    public void addTask(TaskTreeNode p) {
        ProofEnvironment env = p.getProofEnv();
        int size = getChildCount(getRoot());
        for (int i = 0; i < size; i++) {
            MutableTreeNode envNode = (MutableTreeNode) getChild(getRoot(), i);
            if (env.equals(((EnvNode) envNode).getProofEnv())) {
                p.insertNode(this, envNode);
                updateProofToTask(p);
                return;
            }
        } // env not present yet
        EnvNode envNode = new EnvNode(env);
        insertNodeInto(envNode, (MutableTreeNode) getRoot(), size);
        updateProofToTask(p);
        p.insertNode(this, envNode);
    }

    public void removeTask(TaskTreeNode p) {
        Proof[] allProofs = p.allProofs();
        for (Proof allProof : allProofs) {
            proofToTask.remove(allProof);
            p.decoupleFromEnv();
        }
        ProofEnvironment env = p.getProofEnv();
        if (p.getParent().getChildCount() == 1) { // remove env if p is single
            env = null;
            p = (TaskTreeNode) p.getParent();
        }
        if (p.getParent() != null) { // Make sure that p has a parent, because otherwise throws
                                     // removeNodeFromParent(p): java.lang.IllegalArgumentException:
                                     // node does not have a parent.
            removeNodeFromParent(p);
        }

        if (env != null && !env.getProofs().isEmpty()) {
            env.getProofs().iterator().next().getProofs()[0].mgt().updateProofStatus();
        }
    }

    private void updateProofToTask(TaskTreeNode p) {
        proofToTask.put(p.proof(), p);
        for (TaskTreeNode child : p.getChildren()) {
            updateProofToTask(child);
        }
    }

    public TaskTreeNode getTaskForProof(Proof p) {
        if (p == null) {
            return null;
        }
        return proofToTask.get(p);
    }

    public TaskTreeNode addProof(ProofAggregate plist) {
        TaskTreeNode bp;
        if (plist.size() == 1) {
            bp = new BasicTask(plist);
        } else {
            bp = new ProofAggregateTask(plist);
        }
        addTask(bp);
        return bp;
    }
}
