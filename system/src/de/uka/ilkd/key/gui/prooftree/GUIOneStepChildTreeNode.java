// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2011 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.gui.prooftree;

import javax.swing.tree.TreeNode;

import de.uka.ilkd.key.rule.RuleApp;

/**
 * A specieal kind of gui proof tree node to show intermediate intermediate steps of the 
 * {@link de.uka.ilkd.key.rule.OneStepSimplifier}.
 * 
 * These nodes are leaves.
 */
public class GUIOneStepChildTreeNode extends GUIAbstractTreeNode {

    private final RuleApp app;
    private final GUIAbstractTreeNode parent;

    public GUIOneStepChildTreeNode(GUIProofTreeModel tree, GUIAbstractTreeNode parent, RuleApp app) {
        super(tree, parent.getNode());
        this.parent = parent;
        this.app = app;
    }

    @Override public TreeNode getChildAt(int childIndex) {
        return null;
    }

    @Override public int getChildCount() {
        return 0;
    }

    @Override public TreeNode getParent() {
        return parent;
    }

    @Override public boolean isLeaf() {
        return true;
    }
    
    @Override public String toString() {
        // TODO use a pretty printer here
        return app.rule().name() + " @ " + app.posInOccurrence().subTerm();
    }
}

