/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.prooftree;

import javax.annotation.Nonnull;
import javax.swing.tree.TreeNode;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.rule.RuleApp;

/**
 * A special kind of gui proof tree node to show intermediate intermediate steps of the
 * {@link de.uka.ilkd.key.rule.OneStepSimplifier}.
 *
 * These nodes are leaves.
 */
public class GUIOneStepChildTreeNode extends GUIAbstractTreeNode {

    private final RuleApp app;
    private final GUIAbstractTreeNode parent;

    public GUIOneStepChildTreeNode(GUIProofTreeModel tree, GUIAbstractTreeNode parent,
            RuleApp app) {
        super(tree, parent.getNode());
        this.parent = parent;
        this.app = app;
    }

    @Override
    public TreeNode getChildAt(int childIndex) {
        return null;
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

    @Override
    public String toString() {
        // For prettyprinting
        Services services = parent.getNode().proof().getServices();
        String prettySubTerm =
            LogicPrinter.quickPrintTerm(app.posInOccurrence().subTerm(), services);
        return app.rule().name() + " ON " + prettySubTerm;
    }

    public RuleApp getRuleApp() {
        return app;
    }

    @Override
    public void flushCache() {
        // nothing to do
    }

    @Nonnull
    @Override
    public String getSearchString() {
        return toString();
    }
}
