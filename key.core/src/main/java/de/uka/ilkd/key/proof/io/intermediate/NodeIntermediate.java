/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */

package de.uka.ilkd.key.proof.io.intermediate;

import java.util.LinkedList;

/**
 * Node in an intermediate proof representation. Responsible for
 * storing information about children of nodes.
 *
 * @author Dominic Scheurer
 */
public abstract class NodeIntermediate {

    private LinkedList<NodeIntermediate> children =
        new LinkedList<NodeIntermediate>();

    public LinkedList<NodeIntermediate> getChildren() {
        return children;
    }

    public void setChildren(LinkedList<NodeIntermediate> children) {
        this.children = children;
    }

    public void addChild(NodeIntermediate child) {
        this.children.add(child);
    }
}
