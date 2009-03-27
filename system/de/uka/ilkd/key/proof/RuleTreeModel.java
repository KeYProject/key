// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//


package de.uka.ilkd.key.proof;

import java.util.*;

import javax.swing.tree.DefaultMutableTreeNode;
import javax.swing.tree.DefaultTreeModel;
import javax.swing.tree.MutableTreeNode;

import de.uka.ilkd.key.proof.mgt.ProofCorrectnessMgt;
import de.uka.ilkd.key.proof.mgt.RuleJustification;
import de.uka.ilkd.key.rule.*;

public class RuleTreeModel extends DefaultTreeModel {
    
    protected Goal goal;
    protected MutableTreeNode builtInRoot 
    = new DefaultMutableTreeNode("Built-In");
    protected MutableTreeNode axiomTacletRoot 
    = new DefaultMutableTreeNode("Taclet Base");
    protected MutableTreeNode proveableTacletsRoot 
    = new DefaultMutableTreeNode("Lemmas");
    
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
        final List<NoPosTacletApp> apps = 
            sort(getTacletIndex().allNoPosTacletApps());
        for (final NoPosTacletApp app : apps) {
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
    
    private List<NoPosTacletApp> sort(SetOfNoPosTacletApp apps) {
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
}
