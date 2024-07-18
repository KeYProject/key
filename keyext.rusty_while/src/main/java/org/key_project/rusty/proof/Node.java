/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.proof;

import java.util.ArrayList;

import org.key_project.rusty.logic.Sequent;

import org.jspecify.annotations.Nullable;

public class Node {
    /** the proof the node belongs to */
    private final Proof proof;

    /** The parent node. **/
    private @Nullable Node parent = null;

    private Sequent seq = Sequent.EMPTY_SEQUENT;

    private final ArrayList<Node> children = new ArrayList<>(1);

    private boolean closed = false;

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
    public Node(Proof proof, Sequent seq, Node parent) {
        this(proof, seq);
        this.parent = parent;
    }
}
