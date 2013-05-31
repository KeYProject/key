// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
// 


package de.uka.ilkd.key.gui.prooftree;

import javax.swing.tree.TreeNode;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.pp.LogicPrinter;
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
    	//For prettyprinting
    	Services services = parent.getNode().proof().getServices();
    	String prettySubTerm =  LogicPrinter.quickPrintTerm(app.posInOccurrence().subTerm(), services);
        return app.rule().name() + " ON " +prettySubTerm;
    }

    @Override public void flushCache() {
        // nothing to do
    }
}

