/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.prooftree;

import javax.swing.tree.TreeNode;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.proof.Node;

import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.rules.RuleApp;

import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.NullMarked;

/**
 * A special kind of gui proof tree node to show intermediate steps of the
 * {@link de.uka.ilkd.key.rule.OneStepSimplifier}.
 *
 * These nodes are leaves.
 */
@NullMarked
public class GUIOneStepChildTreeNode extends GUIAbstractTreeNode {

    private final RuleApp app;
    private final int formulaNr;
    private final GUIAbstractTreeNode parent;

    public GUIOneStepChildTreeNode(GUIProofTreeModel tree, GUIAbstractTreeNode parent,
            RuleApp app, int formulaNr) {
        super(tree, requireNode(parent));
        this.parent = parent;
        this.app = app;
        this.formulaNr = formulaNr;
    }

    /**
     * @return the proof node wrapped by {@code parent}; the original code dereferences it
     *         directly, so a missing node is a null-pointer failure.
     */
    private static Node requireNode(GUIAbstractTreeNode parent) {
        Node node = parent.getNode();
        if (node == null) {
            // a tree node always wraps a proof node; the original code dereferences it
            throw new NullPointerException("No proof node available.");
        }
        return node;
    }

    /**
     * Returns the child of this node at {@code childIndex}.
     *
     * <p>
     * The JDK declares a non-null return, although this node is a leaf and reports {@code null}
     * for every index; the swing tree never queries children of a leaf, so the {@code null} is
     * never observed, suppressed with a scoped key.
     */
    @SuppressWarnings("nullness:return.type.incompatible")
    @Override
    public TreeNode getChildAt(int childIndex) {
        // this node is a leaf, so the swing model never queries a child of it
        return (TreeNode) null;
    }

    @Override
    public int getChildCount() {
        return 0;
    }

    @Override
    public TreeNode getParent() {
        return parent;
    }

    @Override
    public boolean isLeaf() {
        return true;
    }

    /**
     * The node's label without the applied on information.
     * The term is shown in the tooltip and can still be
     * searched through {@link #getSearchString()}.
     */
    @Override
    public String toString() {
        return app.rule().name().toString();
    }

    public RuleApp getRuleApp() {
        return app;
    }

    public int getFormulaNr() {
        return formulaNr;
    }

    @Override
    public void flushCache() {
        // nothing to do
    }

    @Override
    public @NonNull String getSearchString() {
        Node node = parent.getNode();
        if (node == null) {
            // a tree node always wraps a proof node; the original code dereferences it
            throw new NullPointerException("No proof node available.");
        }
        Services services = node.proof().getServices();
        PosInOccurrence pio = app.posInOccurrence();
        if (pio == null) {
            // a rule app of a one-step-simplification step always carries its position
            throw new NullPointerException("No position in occurrence available.");
        }
        String prettySubTerm = LogicPrinter.quickPrintTerm((JTerm) pio.subTerm(), services);
        return app.rule().name() + " ON " + prettySubTerm;
    }
}
