/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.proof.delayedcut;

import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;

/**
 * Simple immutable structure encapsulating a Node-Goal pair.
 *
 * @author Benjamin Niedermann
 */
public class NodeGoalPair {
    public final Node node;
    public final Goal goal;

    public NodeGoalPair(Node node, Goal goal) {
        this.node = node;
        this.goal = goal;
    }

}
