package org.key_project.slicing;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.List;

import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.PosRuleApp;
import de.uka.ilkd.key.rule.Rule;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.Taclet;

import org.key_project.slicing.graph.DependencyGraph;

public final class ProofRegroup {
    private static final List<List<String>> GROUPS =
        List.of(List.of("alpha", "delta"), List.of("negationNormalForm", "conjNormalForm"),
            List.of("polySimp_expand", "polySimp_normalise", "polySimp_newSym",
                "polySimp_pullOutGcd", "polySimp_applyEq", "polySimp_applyEqRigid",
                "simplify_literals"));

    public static void regroupProof(Proof proof, DependencyGraph graph) {
        /*
         * alpha, delta
         * negationNormalForm, conjNormalForm
         * polySimp_*, inEqSimp_*, simplify_literals
         *
         * simplify_enlarging, simplify, simplify_select
         */
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
            if (rule instanceof Taclet) {
                var ruleSets = ((Taclet) rule).getRuleSets();
                int matchingGroup = -1;
                for (var name : ruleSets) {
                    for (int i = 0; i < GROUPS.size(); i++) {
                        if (GROUPS.get(i).contains(name.toString())) {
                            matchingGroup = i;
                            break;
                        }
                    }
                }
                if (matchingGroup != -1) {
                    List<Node> group = new ArrayList<>();
                    group.add(n);
                    while (true) {
                        if (n.childrenCount() != 1) {
                            break;
                        }
                        var n2 = n.child(0);
                        var r2 = n2.getAppliedRuleApp();
                        var rule2 = r2.rule();
                        if (r2 instanceof PosRuleApp && rule2 instanceof Taclet) {
                            var p2 = (PosRuleApp) r2;
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
                                if (GROUPS.get(matchingGroup).contains(name.toString())) {
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
                        System.out.println("found group ending @ " + n.serialNr());
                        group.get(0).setGroup(group);
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
    }
}
