/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui;

import java.util.*;
import javax.swing.tree.DefaultTreeModel;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.mgt.RuleJustification;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.rule.NoPosTacletApp;
import de.uka.ilkd.key.rule.OneStepSimplifier;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.util.MiscTools;
import de.uka.ilkd.key.util.XMLResources;

/**
 * Extension of {@link DefaultTreeModel} used by {@link InfoTree}.
 *
 * @author Kai Wallisch <kai.wallisch@ira.uka.de>
 */
public class InfoTreeModel extends DefaultTreeModel {

    /**
     *
     */
    private static final long serialVersionUID = 2093787874117871875L;
    private static final String LEMMAS = "Lemmas";
    private static final String TACLET_BASE = "Taclet Base";

    public InfoTreeModel(Goal goal, XMLResources xmlResources, MainWindow mainWindow) {
        super(new InfoTreeNode());
        insertAsLast(new RulesNode(xmlResources.getRuleExplanations(), goal), (InfoTreeNode) root);
        insertAsLast(new TermLabelsNode(mainWindow, xmlResources.getTermLabelExplanations()),
            (InfoTreeNode) root);
        insertAsLast(new FunctionsNode(xmlResources.getFunctionExplanations()),
            (InfoTreeNode) root);
    }

    private void insertAsLast(InfoTreeNode ins, InfoTreeNode parent) {
        insertNodeInto(ins, parent, parent.getChildCount());
    }

    private class FunctionsNode extends InfoTreeNode {

        /**
         *
         */
        private static final long serialVersionUID = -5546552277804988834L;
        private static final String COLLECTION =
            "This node stands for a category of symbols; expand it to browse the symbols "
                + "in the category.";
        private static final String DEFAULT_FUNCTIONS_LABEL =
            "Display descriptions for documented interpreted function and predicate symbols.";

        FunctionsNode(Properties functionExplanations) {
            super("Function Symbols", DEFAULT_FUNCTIONS_LABEL);

            Map<String, InfoTreeNode> categoryMap = new HashMap<>();

            List<String> sortedKeys =
                new ArrayList<>(functionExplanations.stringPropertyNames());
            java.util.Collections.sort(sortedKeys);

            for (String key : sortedKeys) {
                String[] parts = key.split("/", 2);
                if (parts.length == 1) {
                    // no "/"
                    insertAsLast(new InfoTreeNode(key, functionExplanations), this);
                } else {
                    String category = parts[0];
                    InfoTreeNode categoryNode = categoryMap.get(category);
                    if (categoryNode == null) {
                        categoryNode = new InfoTreeNode(category, COLLECTION);
                        categoryMap.put(category, categoryNode);
                        insertAsLast(categoryNode, this);
                    }
                    String description = functionExplanations.getProperty(key);
                    insertAsLast(new InfoTreeNode(parts[1], description), categoryNode);
                }
            }
        }
    }

    private class TermLabelsNode extends InfoTreeNode {

        /**
         *
         */
        private static final long serialVersionUID = 7447092361863294242L;

        TermLabelsNode(MainWindow mainWindow, Properties termLabelExplanations) {
            super("Term Labels", "Show descriptions for currently available term labels.");

            List<Name> labelNames = mainWindow.getSortedTermLabelNames();
            for (Name name : labelNames) {
                insertAsLast(new InfoTreeNode(name.toString(), termLabelExplanations), this);
            }
        }
    }

    private class RulesNode extends InfoTreeNode {

        /**
         *
         */
        private static final long serialVersionUID = 7622830441420768861L;

        RulesNode(Properties ruleExplanations, Goal goal) {
            super("Rules", "Browse descriptions for currently available rules.");

            InfoTreeNode builtInRoot = new InfoTreeNode("Built-In", ruleExplanations);
            insertAsLast(builtInRoot, this);
            InfoTreeNode axiomTacletRoot = new InfoTreeNode(TACLET_BASE, ruleExplanations);
            insertAsLast(axiomTacletRoot, this);
            InfoTreeNode proveableTacletsRoot = new InfoTreeNode(LEMMAS, ruleExplanations);
            insertAsLast(proveableTacletsRoot, this);

            if (goal != null && goal.proof() != null && goal.proof().mgt() != null) {
                for (final BuiltInRule br : goal.ruleAppIndex().builtInRuleAppIndex()
                        .builtInRuleIndex().rules()) {
                    insertAsLast(new InfoTreeNode(br, ruleExplanations), builtInRoot);
                }
                Set<NoPosTacletApp> set = goal.ruleAppIndex().tacletIndex().allNoPosTacletApps();
                OneStepSimplifier simplifier = MiscTools.findOneStepSimplifier(goal.proof());
                if (simplifier != null && !simplifier.isShutdown()) {
                    set.addAll(simplifier.getCapturedTaclets());
                }

                for (final NoPosTacletApp app : sort(set)) {
                    RuleJustification just = goal.proof().mgt().getJustification(app);
                    if (just == null) {
                        continue; // do not break system because of this
                    }
                    if (just.isAxiomJustification()) {
                        insertAndGroup(new InfoTreeNode(app.taclet()), axiomTacletRoot,
                            ruleExplanations);
                    } else {
                        insertAndGroup(new InfoTreeNode(app.taclet()), proveableTacletsRoot,
                            ruleExplanations);
                    }
                }
            }

            axiomTacletRoot
                    .setUserObject(TACLET_BASE + " (" + getChildCount(axiomTacletRoot) + ")");
            proveableTacletsRoot
                    .setUserObject(LEMMAS + " (" + getChildCount(proveableTacletsRoot) + ")");
        }

        private int getChildCount(InfoTreeNode root) {
            int res = 0;
            for (int i = 0; i < root.getChildCount(); i++) {
                final InfoTreeNode child = (InfoTreeNode) root.getChildAt(i);
                // there is no deeper nesting
                final int grandchildren = child.getChildCount();
                res += grandchildren == 0 ? 1 : grandchildren;
            }
            return res;
        }

        /**
         * groups subsequent insertions with the same name under a new node
         */
        private void insertAndGroup(InfoTreeNode ins, InfoTreeNode parent,
                Properties ruleExplanations) {
            InfoTreeNode insNode = ins;
            if (parent.getChildCount() > 0) {
                InfoTreeNode lastNode =
                    (InfoTreeNode) parent.getChildAt(parent.getChildCount() - 1);
                if (getName(insNode).equals(getName(lastNode))) {
                    if (lastNode.getChildCount() == 0) {
                        removeNodeFromParent(lastNode);
                        InfoTreeNode oldParent = parent;
                        parent = new InfoTreeNode(getName(insNode), ruleExplanations);
                        insNode.setTitleToAltName();
                        lastNode.setTitleToAltName();
                        insertAsLast(parent, oldParent);
                        insertAsLast(lastNode, parent);
                    } else {
                        parent = lastNode;
                        insNode.setTitleToAltName();
                    }
                }
            }
            insertAsLast(ins, parent);
        }

        private String getName(InfoTreeNode t1) {
            if (t1.getUserObject() instanceof Taclet) {
                return ((Taclet) t1.getUserObject()).displayName();
            } else {
                String title = t1.toString();

                // strip number of taclets
                int parenIdx = title.lastIndexOf('(');
                if (parenIdx >= 0) {
                    return title.substring(0, parenIdx - 1).intern();
                } else {
                    return title;
                }
            }
        }

        private List<NoPosTacletApp> sort(Set<NoPosTacletApp> set) {
            final ArrayList<NoPosTacletApp> l = new ArrayList<>(set);

            l.sort((o1, o2) -> {
                final Taclet t1 = o1.taclet();
                final Taclet t2 = o2.taclet();
                return t1.displayName().compareTo(t2.displayName());
            });
            return l;
        }
    }

}
