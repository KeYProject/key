/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.slicing;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.List;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.PosRuleApp;
import de.uka.ilkd.key.rule.Rule;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.Taclet;

import org.key_project.slicing.graph.DependencyGraph;

/**
 * Proof step regrouping functionality.
 *
 * @author Arne Keller
 */
public final class ProofRegroup {
    private ProofRegroup() {

    }

    public static void regroupProof(Proof proof, DependencyGraph graph) {
        /*
         * alpha, delta
         * negationNormalForm, conjNormalForm
         * polySimp_*, inEqSimp_*, simplify_literals
         *
         * simplify_enlarging, simplify, simplify_select
         */
        var groups = ProofRegroupSettingsProvider.getSettings().getGroups();
        Deque<Node> q = new ArrayDeque<>();
        q.add(proof.root());
        while (!q.isEmpty()) {
            Node n = q.pop();
            if (n.childrenCount() == 0) {
                continue;
            }
            RuleApp r = n.getAppliedRuleApp();
            if (r == null) {
                continue;
            }
            Rule rule = r.rule();
            if (rule instanceof Taclet taclet) {
                var ruleSets = taclet.getRuleSets();
                String matchingGroup = null;
                for (var name : ruleSets) {
                    for (String i : groups.keySet()) {
                        if (groups.get(i).contains(name.toString())) {
                            matchingGroup = i;
                            break;
                        }
                    }
                }
                if (matchingGroup != null) {
                    List<Node> group = new ArrayList<>();
                    group.add(n);
                    while (true) {
                        if (n.childrenCount() != 1) {
                            break;
                        }
                        var n2 = n.child(0);
                        var r2 = n2.getAppliedRuleApp();
                        var rule2 = r2.rule();
                        if (r2 instanceof PosRuleApp p2 && rule2 instanceof Taclet) {
                            var graphNode = graph.getGraphNode(proof, n2.getBranchLocation(),
                                p2.posInOccurrence());
                            Node finalN = n;
                            if (graph.edgesProducing(graphNode)
                                    .noneMatch(a -> a.getProofStep() == finalN)) {
                                break;
                            }
                            var ruleSets2 = ((Taclet) rule2).getRuleSets();
                            var found = false;
                            for (var name : ruleSets2) {
                                if (groups.get(matchingGroup).contains(name.toString())) {
                                    found = true;
                                    break;
                                }
                            }
                            if (!found) {
                                break;
                            }
                            group.add(n2);
                            n = n2;
                        } else {
                            break;
                        }
                    }
                    if (group.size() > 1) {
                        group.get(0).setGroup(group);
                        group.get(0).setExtraNodeLabel(matchingGroup);
                        for (int i = 1; i < group.size(); i++) {
                            group.get(i).setHideInProofTree(true);
                        }
                    }
                }
            }
            for (int i = 0; i < n.childrenCount(); i++) {
                q.add(n.child(i));
            }
        }
        // make sure the changed structure is visible
        MainWindow.getInstance().getProofTreeView().getDelegateModel().updateTree(null);
    }
}
