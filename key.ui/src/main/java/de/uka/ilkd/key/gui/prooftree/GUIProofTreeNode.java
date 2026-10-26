/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.prooftree;
/**
 * this class implements a TreeModel that can be displayed using the JTree class framework
 */

import javax.swing.tree.TreeNode;

import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.rule.OneStepSimplifier.Protocol;
import de.uka.ilkd.key.rule.OneStepSimplifierRuleApp;

import org.key_project.prover.sequent.PosInOccurrence;

import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

@NullMarked
class GUIProofTreeNode extends GUIAbstractTreeNode {

    /** Children of this node; {@code null} until they have been computed. */
    private GUIAbstractTreeNode @Nullable [] children;

    public GUIProofTreeNode(GUIProofTreeModel tree, Node node) {
        super(tree, node);
    }

    public TreeNode getChildAt(int childIndex) {
        ensureChildrenArray();
        GUIAbstractTreeNode[] childArray = children;
        if (childArray == null) {
            // ensureChildrenArray always establishes the children array
            throw new NullPointerException("No children array available.");
        }
        return childArray[childIndex];
    }

    public int getChildCount() {
        ensureChildrenArray();
        GUIAbstractTreeNode[] childArray = children;
        if (childArray == null) {
            // ensureChildrenArray always establishes the children array
            throw new NullPointerException("No children array available.");
        }
        return childArray.length;
    }

    /**
     * Returns the parent of this node.
     *
     * <p>
     * The JDK declares a non-null return, although a node whose wrapped proof node was collected
     * reports {@code null}; the swing tree only ever holds live nodes, so this is not reached on
     * the happy path, suppressed with a scoped key.
     */
    @SuppressWarnings("nullness:return.type.incompatible")
    @Override
    public TreeNode getParent() {
        TreeNode parentNode = parent;
        if (parentNode != null) {
            return parentNode;
        }
        // more complicated general case
        Node n = getNode();
        if (n == null) {
            return (TreeNode) null;
        }
        Node next = n.parent();
        while (next != null && findChild(next) != null) {
            n = next;
            next = n.parent();
        }
        return findBranch(n);
    }

    @Override
    public boolean isLeaf() {
        return getChildCount() == 0;
    }

    public String toString() {
        // changed to serial:name for searching
        // the proof tree in ProofTreeView.java
        Node n = getNode();
        if (n != null) {
            return n.serialNr() + ":" + n.name();
        } else {
            return "Invalid WeakReference";
        }
    }

    /**
     * Ensure that the children array is valid.
     *
     * Nodes may have children if they represent a One step simplification. If so, the array of
     * children is read from the rule app object
     */
    private void ensureChildrenArray() {
        if (children == null) {
            Node node = getNode();
            if (node != null
                    && node.getAppliedRuleApp() instanceof OneStepSimplifierRuleApp ruleApp) {
                Protocol protocol = ruleApp.getProtocol();
                if (protocol != null) {
                    PosInOccurrence pio = ruleApp.posInOccurrence();
                    if (pio == null) {
                        // a one-step-simplification rule app always carries its position
                        throw new NullPointerException("No position in occurrence available.");
                    }
                    GUIAbstractTreeNode[] childArray = new GUIAbstractTreeNode[protocol.size()];
                    children = childArray;
                    for (int i = 0; i < childArray.length; i++) {
                        childArray[i] =
                            new GUIOneStepChildTreeNode(getProofTreeModel(), this, protocol.get(i),
                                node.sequent().formulaNumberInSequent(pio));
                        childArray[i].setParent(this);
                    }
                    return;
                }
            }

            // otherwise
            children = new GUIAbstractTreeNode[0];
        }
    }

    @Override
    public void flushCache() {
        children = null;
    }

    @Override
    public @NonNull String getSearchString() {
        return toString();
    }
}
