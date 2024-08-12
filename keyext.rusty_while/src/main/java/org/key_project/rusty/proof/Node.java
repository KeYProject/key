/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.proof;

import java.util.ArrayList;
import java.util.Collections;

import org.key_project.rusty.logic.Sequent;
import org.key_project.rusty.rule.NoPosTacletApp;
import org.key_project.rusty.rule.RuleApp;
import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableSet;

import org.jspecify.annotations.Nullable;

public class Node {
    /** the proof the node belongs to */
    private final Proof proof;

    /** The parent node. **/
    private @Nullable Node parent = null;

    private Sequent seq = Sequent.EMPTY_SEQUENT;

    private final ArrayList<Node> children = new ArrayList<>(1);

    private boolean closed = false;

    private RuleApp appliedRuleApp;

    /**
     * Sibling number of this proof node.
     * If the {@link #parent()} proof node has more than one child node,
     * each child node receives an index (starting at 0, incrementing by 1 for each sibling).
     */
    private int siblingNr = -1;

    /**
     * If the rule base has been extended e.g. by loading a new taclet as lemma or by applying a
     * taclet with an addrule section on this node, then these taclets are stored in this list
     */
    private ImmutableSet<NoPosTacletApp> localIntroducedRules =
        DefaultImmutableSet.nil();

    /**
     * creates an empty node that is root and leaf.
     */
    public Node(Proof proof) {
        this.proof = proof;
    }

    /**
     * creates a node with the given contents and associated proof
     */
    public Node(Proof proof, Sequent seq) {
        this(proof);
        this.seq = seq;
    }

    /**
     * creates a node with the given contents, the given collection of children (all elements must
     * be of class Node) and the given parent node.
     */
    public Node(Proof proof, Sequent seq, @Nullable Node parent) {
        this(proof, seq);
        this.parent = parent;
    }

    /**
     * sets the sequent at this node
     */
    public void setSequent(Sequent seq) {
        this.seq = seq;
    }

    /** returns the sequent of this node */
    public Sequent sequent() {
        return seq;
    }

    /**
     * @return the parent node of this node.
     */
    public @Nullable Node parent() {
        return parent;
    }

    public void setAppliedRuleApp(RuleApp ruleApp) {
        // this.nodeInfo.updateNoteInfo();
        this.appliedRuleApp = ruleApp;
        // clearNameCache();
    }

    public Proof proof() {
        return proof;
    }

    /**
     * Makes the given node a child of this node.
     *
     * @param newChild the node to make a child of this node.
     */
    public void add(Node newChild) {
        newChild.siblingNr = children.size();
        children.add(newChild);
        newChild.parent = this;
    }

    /**
     * Makes the given node children of this node.
     *
     * @param newChildren the node to make into children of this node.
     */
    public void addAll(Node[] newChildren) {
        final int size = children.size();
        for (int i = 0; i < newChildren.length; i++) {
            newChildren[i].siblingNr = i + size;
            newChildren[i].parent = this;
        }

        Collections.addAll(children, newChildren);
        children.trimToSize();
    }

    public StringBuffer getUniqueTacletId() {
        StringBuffer id = new StringBuffer();
        int c = 0;
        Node n = this;

        while (n != null) {
            // c += n.localIntroducedRules.size();

            if (n.parent != null && n.parent.childrenCount() > 1) {
                id.append(n.siblingNr);
            }

            n = n.parent;
        }

        id.append("_").append(c);

        return id;
    }

    /** @return number of children */
    public int childrenCount() {
        return children.size();
    }

    /**
     * adds a new NoPosTacletApp to the set of available NoPosTacletApps at this node
     *
     * @param s the app to add.
     */
    public void addNoPosTacletApp(NoPosTacletApp s) {
        localIntroducedRules = localIntroducedRules.add(s);
    }
}
