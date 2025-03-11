/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof.reference;

import java.util.Set;

import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;

/**
 * Indicates that a branch has been closed by "reference" to another closed proof.
 * This is always looked up using {@link Node#lookup(Class)} on the node of that branch.
 *
 * @param proof The proof referenced.
 * @param node  The node referenced.
 * @param nodesToSkip If the referenced proof has dependency graph information: proof steps to skip.
 * @author Arne Keller
 */
public record ClosedBy(Proof proof, Node node, Set<Node> nodesToSkip) {
}
