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
package de.uka.ilkd.key.gui;

import de.uka.ilkd.key.collection.ImmutableList;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.List;

import javax.swing.tree.DefaultTreeModel;

import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.mgt.RuleJustification;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.rule.NoPosTacletApp;
import de.uka.ilkd.key.rule.OneStepSimplifier;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.util.MiscTools;
import java.util.LinkedList;

public class InfoTreeModel extends DefaultTreeModel {

    private static final String LEMMAS = "Lemmas";
    private static final String TACLET_BASE = "Taclet Base";
    protected final InfoTreeNode builtInRoot;
    protected final InfoTreeNode axiomTacletRoot;
    protected final InfoTreeNode proveableTacletsRoot;
    private final XMLProperties ruleExplanations;

    public InfoTreeModel(Goal goal, XMLProperties ruleExplanations,
            XMLProperties termLabelExplanations, MainWindow mainWindow) {
        super(new InfoTreeNode());

        InfoTreeNode rulesNode = new InfoTreeNode("Rules",
                "Browse descriptions for currently available rules.");
        insertAsLast(rulesNode, (InfoTreeNode) root);

        InfoTreeNode termLabelsNode = new InfoTreeNode("Term Labels",
                "Get descriptions for currently available term labels.");
        insertAsLast(termLabelsNode, (InfoTreeNode) root);

        ImmutableList<Name> labelNamesFromProfile = mainWindow.getMediator()
                .getProfile().getTermLabelManager().getSupportedTermLabelNames();
        List<String> labelNames = new LinkedList();
        for (Name labelName : labelNamesFromProfile) {
            labelNames.add(labelName.toString());
        }
        Collections.sort(labelNames, String.CASE_INSENSITIVE_ORDER);
        for (String name : labelNames) {
            insertAsLast(new InfoTreeNode(name, termLabelExplanations), termLabelsNode);
        }

        this.ruleExplanations = ruleExplanations;

        builtInRoot = new InfoTreeNode("Built-In", ruleExplanations);
        insertAsLast(builtInRoot, rulesNode);
        axiomTacletRoot = new InfoTreeNode(TACLET_BASE, ruleExplanations);
        insertAsLast(axiomTacletRoot, rulesNode);
        proveableTacletsRoot = new InfoTreeNode(LEMMAS, ruleExplanations);
        insertAsLast(proveableTacletsRoot, rulesNode);

        if (goal != null) {
            for (final BuiltInRule br : goal.ruleAppIndex().builtInRuleAppIndex().builtInRuleIndex().rules()) {
                insertAsLast(new InfoTreeNode(br.displayName(), ruleExplanations), builtInRoot);
            }
            ImmutableSet<NoPosTacletApp> set = goal.ruleAppIndex().tacletIndex().allNoPosTacletApps();
            OneStepSimplifier simplifier = MiscTools.findOneStepSimplifier(goal.proof());
            if (simplifier != null) {
                set = set.union(simplifier.getCapturedTaclets());
            }

            for (final NoPosTacletApp app : sort(set)) {
                RuleJustification just = goal.proof().mgt().getJustification(app);
                if (just == null) {
                    continue; // do not break system because of this
                }
                if (just.isAxiomJustification()) {
                    insertAndGroup(new InfoTreeNode(app.taclet()), axiomTacletRoot);
                } else {
                    insertAndGroup(new InfoTreeNode(app.taclet()), proveableTacletsRoot);
                }
            }
        }

        axiomTacletRoot.setUserObject(TACLET_BASE + " (" + getChildCount(axiomTacletRoot) + ")");
        proveableTacletsRoot.setUserObject(LEMMAS + " (" + getChildCount(proveableTacletsRoot) + ")");
    }

    private void insertAsLast(InfoTreeNode ins, InfoTreeNode parent) {
        insertNodeInto(ins, parent, parent.getChildCount());
    }

    /**
     * groups subsequent insertions with the same name under a new node
     */
    private void insertAndGroup(InfoTreeNode ins, InfoTreeNode parent) {
        InfoTreeNode insNode = (InfoTreeNode) ins;
        if (parent.getChildCount() > 0) {
            InfoTreeNode lastNode
                    = (InfoTreeNode) parent.getChildAt(
                            parent.getChildCount() - 1);
            if (getName(insNode).equals(getName(lastNode))) {
                if (lastNode.getChildCount() == 0) {
                    removeNodeFromParent(lastNode);
                    InfoTreeNode oldParent = parent;
                    parent = new InfoTreeNode(getName(insNode), ruleExplanations);
                    insertAsLast(parent, oldParent);
                    insertAsLast(lastNode, parent);
                } else {
                    parent = lastNode;
                }
            }
        }
        insertAsLast(ins, parent);
    }

    private String getName(InfoTreeNode t1) {
        if (t1.getUserObject() instanceof Taclet) {
            return ((Taclet) t1.getUserObject()).displayName();
        } else {
            return t1.toString();
        }
    }

    private List<NoPosTacletApp> sort(ImmutableSet<NoPosTacletApp> apps) {
        final ArrayList<NoPosTacletApp> l
                = new ArrayList<NoPosTacletApp>(apps.size());

        for (final NoPosTacletApp app : apps) {
            l.add(app);
        }

        Collections.sort(l, new Comparator<NoPosTacletApp>() {
            @Override
            public int compare(NoPosTacletApp o1, NoPosTacletApp o2) {
                final Taclet t1 = o1.taclet();
                final Taclet t2 = o2.taclet();
                return t1.displayName().compareTo(t2.displayName());
            }
        });
        return l;
    }

    private static int getChildCount(InfoTreeNode root) {
        int res = 0;
        for (int i = 0; i < root.getChildCount(); i++) {
            final InfoTreeNode child = (InfoTreeNode) root.getChildAt(i);
            // there is no deeper nesting
            final int grandchildren = child.getChildCount();
            res += grandchildren == 0 ? 1 : grandchildren;
        }
        return res;
    }

}
