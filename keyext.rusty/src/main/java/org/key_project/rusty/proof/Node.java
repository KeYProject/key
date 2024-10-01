/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.proof;

import java.util.*;

import org.key_project.rusty.logic.RenamingTable;
import org.key_project.rusty.logic.Sequent;
import org.key_project.rusty.rule.NoPosTacletApp;
import org.key_project.rusty.rule.RuleApp;
import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSet;

import org.jspecify.annotations.Nullable;

public class Node implements Iterable<Node> {
    private static final String NODES = "nodes";

    /** the proof the node belongs to */
    private final Proof proof;

    /** The parent node. **/
    private @Nullable Node parent = null;

    private Sequent seq = Sequent.EMPTY_SEQUENT;

    private final ArrayList<Node> children = new ArrayList<>(1);

    private boolean closed = false;

    private RuleApp appliedRuleApp;

    /**
     * Serial number of this proof node.
     * For each proof, serial numbers are assigned to nodes as they are created:
     * the first step is assigned number 0, the next step number 1, and so on.
     */
    private final int serialNr;

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
    private ImmutableList<RenamingTable> renamings;

    /**
     * creates an empty node that is root and leaf.
     */
    public Node(Proof proof) {
        this.proof = proof;
        serialNr = proof.getServices().getCounter(NODES).getCountPlusPlus();
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

    public int getSerialNr() {
        return serialNr;
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

    /**
     *
     * @param i an index (starting at 0).
     * @return the i-th child of this node.
     */
    public Node child(int i) {
        return children.get(i);
    }

    /**
     * @param child a child of this node.
     * @return the number of the node <code>child</code>, if it is a child of this node (starting
     *         with <code>0</code>), <code>-1</code> otherwise
     */
    public int getChildNr(Node child) {
        int res = 0;
        final Iterator<Node> it = childrenIterator();

        while (it.hasNext()) {
            if (it.next() == child) {
                return res;
            }
            ++res;
        }

        return -1;
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

    public RuleApp getAppliedRuleApp() {
        return appliedRuleApp;
    }

    /**
     * adds a new NoPosTacletApp to the set of available NoPosTacletApps at this node
     *
     * @param s the app to add.
     */
    public void addNoPosTacletApp(NoPosTacletApp s) {
        localIntroducedRules = localIntroducedRules.add(s);
    }

    /** marks a node as closed */
    Node close() {
        closed = true;
        Node tmp = parent;
        Node result = this;
        while (tmp != null && tmp.isCloseable()) {
            tmp.closed = true;
            result = tmp;
            tmp = tmp.parent();
        }
        // clearNameCache();
        return result;
    }

    /** @return true iff this inner node is closeable */
    private boolean isCloseable() {
        assert childrenCount() > 0;
        for (Node child : children) {
            if (!child.isClosed()) {
                return false;
            }
        }
        return true;
    }

    public boolean isClosed() {
        return closed;
    }

    /**
     * @return an iterator for the direct children of this node.
     */
    public Iterator<Node> childrenIterator() {
        return new NodeIterator(children.iterator());
    }

    /**
     * @return an iterator for all nodes in the subtree (including this node).
     */
    public Iterator<Node> subtreeIterator() {
        return new SubtreeIterator(this);
    }

    /**
     * Returns an iterator over this node's children. Use {@link #leavesIterator()} if you need to
     * iterate over leaves instead.
     *
     * @return iterator over children.
     */
    public Iterator<Node> iterator() {
        return childrenIterator();
    }

    /**
     * Computes the leaves of the current subtree and returns them.
     *
     * @return the leaves of the current subtree.
     */
    List<Node> getLeaves() {
        final List<Node> leaves = new LinkedList<>();
        final LinkedList<Node> nodesToCheck = new LinkedList<>();
        nodesToCheck.add(this);
        do {
            final Node n = nodesToCheck.poll();
            if (n.leaf()) {
                leaves.add(n);
            } else {
                nodesToCheck.addAll(0, n.children);
            }
        } while (!nodesToCheck.isEmpty());
        return leaves;
    }

    public boolean leaf() {
        return children.isEmpty();
    }

    /**
     * @return an iterator for the leaves of the subtree below this node. The computation is called
     *         at every call!
     */
    public Iterator<Node> leavesIterator() {
        return new NodeIterator(getLeaves().iterator());
    }

    /**
     * @return number of nodes in the subtree below this node.
     */
    public int countNodes() {
        Iterator<Node> it = subtreeIterator();
        int res = 0;
        for (; it.hasNext(); it.next()) {
            res++;
        }
        return res;
    }

    public void setRenamings(ImmutableList<RenamingTable> list) {
        renamings = list;
    }
}
