/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof.reference;

import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;

/**
 * Indicates that a branch has been closed by "reference" to another closed proof.
 *
 * @author Arne Keller
 */
public class ClosedBy {
    /**
     * The proof referenced.
     */
    private final Proof proof;
    /**
     * The node referenced.
     */
    private final Node node;

    /**
     * Construct a new instance.
     *
     * @param proof the proof
     * @param node the node
     */
    public ClosedBy(Proof proof, Node node) {
        this.proof = proof;
        this.node = node;
    }

    public Proof getProof() {
        return proof;
    }

    public Node getNode() {
        return node;
    }
}
