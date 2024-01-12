/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.api;

import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.NodeInfo;

/**
 * Wrapper for a proof node with utilities methods to
 *
 * @author Sarah Grebing
 * @author Alexander Weigl
 */
public class ProjectedNode {

    private final Node proofNode;

    private final ProjectedNode parent;

    /**
     * Creates the wrapper object for a proof node
     *
     * @param node
     * @param parent
     */
    public ProjectedNode(Node node, ProjectedNode parent) {
        this.proofNode = node;
        this.parent = parent;
    }

    /**
     * Return the sequent of a proof node
     *
     * @return de.uka.ilkd.key.logic.Sequent s
     */
    public Sequent getSequent() {
        return proofNode.sequent();
    }

    public ProjectedNode getParent() {
        return this.parent;
    }

    public boolean isRoot() {
        return getParent() == null;
    }

    public NodeInfo getNodeInfo() {
        return proofNode.getNodeInfo();
    }

    public boolean isPseudoNode() {
        return proofNode == null;
    }

    public Node getProofNode() {
        return proofNode;
    }

    public static ProjectedNode pseudoRoot() {
        return new ProjectedNode(null, null);
    }
}
