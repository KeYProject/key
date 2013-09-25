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



package de.uka.ilkd.key.proof;

import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.List;

import javax.swing.tree.DefaultMutableTreeNode;
import javax.swing.tree.DefaultTreeModel;
import javax.swing.tree.MutableTreeNode;
import javax.swing.tree.TreeNode;

import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.proof.mgt.ProofCorrectnessMgt;
import de.uka.ilkd.key.proof.mgt.RuleJustification;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.rule.NoPosTacletApp;
import de.uka.ilkd.key.rule.OneStepSimplifier;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.util.MiscTools;

public class RuleTreeModel extends DefaultTreeModel {
    
    private static final long serialVersionUID = -7536362498647498639L;
    private static final String LEMMAS = "Lemmas";
    private static final String TACLET_BASE = "Taclet Base";
    protected Goal goal;
    protected MutableTreeNode builtInRoot 
    = new DefaultMutableTreeNode("Built-In");
    protected MutableTreeNode axiomTacletRoot 
    = new DefaultMutableTreeNode(TACLET_BASE);
    protected MutableTreeNode proveableTacletsRoot 
    = new DefaultMutableTreeNode(LEMMAS);
    
    public RuleTreeModel(Goal g) {
        super(new DefaultMutableTreeNode("Rule Base"));
        this.goal = g;
        insertAsLast(builtInRoot, (MutableTreeNode) getRoot());
        insertAsLast(axiomTacletRoot, (MutableTreeNode) getRoot());
        insertAsLast(proveableTacletsRoot, (MutableTreeNode) getRoot());
        if (g!=null) rulesForGoal(g);
    }



    private void insertAsLast(MutableTreeNode ins, MutableTreeNode parent) {
        insertNodeInto(ins, parent, parent.getChildCount());
    }

    /** groups subsequent insertions with the same name under a new node */
    private void insertAndGroup(MutableTreeNode ins, MutableTreeNode parent) {
        DefaultMutableTreeNode insNode = (DefaultMutableTreeNode) ins;
        if (parent.getChildCount()>0) {
            DefaultMutableTreeNode lastNode =
                (DefaultMutableTreeNode)parent.getChildAt(
		    parent.getChildCount()-1);
            if (getName(insNode).equals(getName(lastNode))) {
                if (lastNode.getChildCount()==0) {
                    removeNodeFromParent(lastNode);
                    MutableTreeNode oldParent=parent;
                    parent = new DefaultMutableTreeNode(getName(insNode));
                    insertAsLast(parent, oldParent);
                    insertAsLast(lastNode, parent);
                } else {
                    parent = lastNode;
                }
            }
        }
        insertAsLast(ins, parent);
    }

    
    private String getName(DefaultMutableTreeNode t1) {
        if (t1.getUserObject() instanceof Taclet) {
            return ((Taclet)t1.getUserObject()).displayName();
        } else {
            return t1.toString();
        }
    }


    private void rulesForGoal(Goal g) {
        for (final BuiltInRule br : getBuiltInIndex().rules()) {
            insertAsLast(new DefaultMutableTreeNode(br), builtInRoot);
        }
        ImmutableSet<NoPosTacletApp> set = getTacletIndex().allNoPosTacletApps();
        OneStepSimplifier simplifier = MiscTools.findOneStepSimplifier(g.proof());
        if (simplifier != null) {
           set = set.union(simplifier.getCapturedTaclets());
        }

        for (final NoPosTacletApp app : sort(set)) {
            RuleJustification just = mgt().getJustification(app);
            if (just==null) continue; // do not break system because of this
            if (just.isAxiomJustification()) {
                insertAndGroup(new DefaultMutableTreeNode(app.taclet()), 
                               axiomTacletRoot);
            } else {
                insertAndGroup(new DefaultMutableTreeNode(app.taclet()),
                               proveableTacletsRoot);
            }
        }
    }
    
    private List<NoPosTacletApp> sort(ImmutableSet<NoPosTacletApp> apps) {
        final ArrayList<NoPosTacletApp> l = 
            new ArrayList<NoPosTacletApp>(apps.size());
        
        for (final NoPosTacletApp app : apps) {
            l.add(app);
        }
        
        Collections.sort(l, new Comparator<NoPosTacletApp>() { 
            public int compare(NoPosTacletApp o1, NoPosTacletApp o2) {
                final Taclet t1 = o1.taclet(); 
                final Taclet t2 = o2.taclet();
                return t1.displayName().compareTo(t2.displayName());
            } 
        });
        return l;
    }
    
    private TacletIndex getTacletIndex() {
        return goal.ruleAppIndex().tacletIndex();
    }
    
    private BuiltInRuleIndex getBuiltInIndex() {
        RuleAppIndex ri =  goal.ruleAppIndex();
        return ri.builtInRuleAppIndex().builtInRuleIndex();
    }
    
    public ProofCorrectnessMgt mgt() {
        return goal.proof().mgt();
    }
    
    public void setSelectedGoal(Goal g) {
        goal=g;
    }
    
    public Goal getGoal() {
        return goal;
    }
    
    public void updateTacletCount() {
        axiomTacletRoot.setUserObject(TACLET_BASE+" ("+getAxiomTacletCount()+")");
        proveableTacletsRoot.setUserObject(LEMMAS+" ("+getLemmaTacletCount()+")");
    }
    
    public int getAxiomTacletCount(){
        return getChildCount(axiomTacletRoot);
    }
    
    public int getLemmaTacletCount(){
        return getChildCount(proveableTacletsRoot);
    }

    private static int getChildCount(MutableTreeNode root) {
        int res = 0;
        for (int i= 0; i < root.getChildCount(); i++) {
            final TreeNode child = root.getChildAt(i);
            // there is no deeper nesting
            final int grandchildren = child.getChildCount();
            res += grandchildren==0? 1: grandchildren;
        }
        return res;
    }
}
