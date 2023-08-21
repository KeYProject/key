/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof.mgt;

import javax.swing.tree.DefaultMutableTreeNode;
import javax.swing.tree.MutableTreeNode;

import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.proof.SingleProof;

public class ProofAggregateTask extends DefaultMutableTreeNode implements TaskTreeNode {

    /**
     *
     */
    private static final long serialVersionUID = 2292876929382788414L;
    private final TaskTreeNode[] proofs;
    private final ProofAggregate proofList;
    private final String descr;

    public ProofAggregateTask(ProofAggregate ps) {
        super(ps);
        proofs = new TaskTreeNode[ps.size()];
        for (int i = 0; i < ps.size(); i++) {
            if (ps.getChildrenAt(i) instanceof SingleProof) {
                proofs[i] = new BasicTask(ps.getChildrenAt(i));
            } else {
                proofs[i] = new ProofAggregateTask(ps.getChildrenAt(i));
            }
        }
        proofList = ps;
        descr = ps.description();
    }

    public String shortDescr() {
        return descr;
    }

    public String toString() {
        return shortDescr();
    }

    public ProofEnvironment getProofEnv() {
        return proofs[0].proof().getEnv();
    }

    public ProofAggregate getProofList() {
        return proofList;
    }

    public Proof proof() {
        return proofs[0].proof();
    }

    public Proof[] allProofs() {
        return getProofList().getProofs();
    }

    public void insertNode(TaskTreeModel model, MutableTreeNode parentNode) {
        model.insertNodeInto(this, parentNode, model.getChildCount(parentNode));
        for (TaskTreeNode proof : proofs) {
            proof.insertNode(model, this);
        }
    }

    public ProofStatus getStatus() {
        return proofList.getStatus();
    }

    public void decoupleFromEnv() {
        getProofEnv().removeProofList(proofList);
    }

    @Override
    public TaskTreeNode[] getChildren() {
        return proofs;
    }
}
