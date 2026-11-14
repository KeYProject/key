/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.proof.mgt;

import javax.swing.tree.DefaultMutableTreeNode;
import javax.swing.tree.MutableTreeNode;

import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofAggregate;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

/**
 * Captures a node in the TaskTree which contains exactly one proof. Such a node is the only one
 * with a one to one mapping between TaskTreeNode and Proof. It may be a sub task of a more complex
 * task such as ProofListTask.
 */
@NullMarked
public class BasicTask extends DefaultMutableTreeNode implements TaskTreeNode {

    /**
     *
     */
    private static final long serialVersionUID = -6490453248054760812L;
    private final ProofAggregate proof;

    /**
     * creates a task with a single proof. The given proof list must contain exactly one proof.
     */
    public BasicTask(ProofAggregate pl) {
        super(pl);
        proof = pl;
    }

    public String shortDescr() {
        Proof p = proof();
        if (p == null) {
            // a basic task always wraps a proof; the original code dereferences it
            throw new NullPointerException("No proof available.");
        }
        return p.name().toString();
    }

    public String toString() {
        return shortDescr();
    }

    public ProofEnvironment getProofEnv() {
        Proof p = proof();
        if (p == null) {
            // a basic task always wraps a proof; the original code dereferences it
            throw new NullPointerException("No proof available.");
        }
        ProofEnvironment env = p.getEnv();
        if (env == null) {
            // a proof always knows its environment; the original code returned it directly
            throw new NullPointerException("No proof environment available.");
        }
        return env;
    }

    /* returns the single proof of this task */
    public @Nullable Proof proof() {
        return proof.getFirstProof();
    }

    /** returns all proofs attached to this basic task */
    public @Nullable Proof[] allProofs() {
        return new Proof[] { proof() };
    }

    /** inserts a node given the task tree model and a parent node */
    public void insertNode(TaskTreeModel model, MutableTreeNode parentNode) {
        model.insertNodeInto(this, parentNode, model.getChildCount(parentNode));
    }

    /**
     * asks the proof management component of the associated proofs for the status of the associated
     * proof .
     */
    public ProofStatus getStatus() {
        Proof p = proof();
        if (p == null) {
            // a basic task always wraps a proof; the original code dereferences it
            throw new NullPointerException("No proof available.");
        }
        ProofCorrectnessMgt mgt = p.mgt();
        if (mgt == null) {
            // every proof carries its correctness management object
            throw new NullPointerException("No proof management available.");
        }
        return mgt.getStatus();
    }

    /** returns the upper most task this basic task belongs to. */
    public TaskTreeNode getRootTask() {
        TaskTreeNode tn = this;
        while (!(tn.getParent() instanceof EnvNode)) {
            tn = (TaskTreeNode) tn.getParent();
        }
        return tn;
    }

    /** removes the associated proof from their environment */
    public void decoupleFromEnv() {
        getProofEnv().removeProofList(proof);
    }

    @Override
    public TaskTreeNode[] getChildren() {
        return NO_CHILDREN;
    }
}
