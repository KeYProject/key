/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof.reference;

import java.util.*;
import java.util.stream.Collectors;

import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.EqualityModuloProofIrrelevancy;
import de.uka.ilkd.key.rule.NoPosTacletApp;
import de.uka.ilkd.key.rule.merge.CloseAfterMerge;

import org.key_project.prover.sequent.Semisequent;
import org.key_project.prover.sequent.Sequent;
import org.key_project.prover.sequent.SequentFormula;
import org.key_project.slicing.DependencyTracker;
import org.key_project.slicing.analysis.AnalysisResults;

/**
 * Utility class for proof caching.
 *
 * @author Arne Keller
 */
public final class ReferenceSearcher {
    private ReferenceSearcher() {

    }

    /**
     * Try to find a closed branch in another proof that is equivalent to the <code>newNode</code>.
     *
     * @param previousProofs old proofs
     * @param newNode new node (must be an open goal)
     * @return a reference (or null, if none found)
     */
    public static ClosedBy findPreviousProof(List<Proof> previousProofs, Node newNode) {
        // first verify that the new node does not contain any terms that depend on external
        // influences
        if (!suitableForCloseByReference(newNode)) {
            return null;
        }
        for (int i = 0; i < previousProofs.size(); i++) {
            Proof p = previousProofs.get(i);
            if (p == newNode.proof()) {
                continue; // doesn't make sense to cache in the same proof
            }
            // conservative check: all user-defined rules in a previous proof
            // have to also be available in the new proof
            var proofFile = p.getProofFile() != null ? p.getProofFile().toString() : "////";
            var tacletIndex = p.allGoals().head().ruleAppIndex().tacletIndex();
            var newTacletIndex = newNode.proof().allGoals().head().ruleAppIndex().tacletIndex();
            Set<NoPosTacletApp> newTaclets = newTacletIndex.allNoPosTacletApps();
            var tacletsOk = true;
            for (var taclet : tacletIndex.allNoPosTacletApps().stream()
                    .filter(x -> x.taclet().getOrigin() != null
                            && x.taclet().getOrigin().contains(proofFile))
                    .toList()) {
                if (newTaclets.stream().noneMatch(newTaclet -> Objects
                        .equals(taclet.taclet().toString(), newTaclet.taclet().toString()))) {
                    tacletsOk = false;
                    break;
                }
            }
            if (!tacletsOk) {
                continue;
            }

            // only search in compatible proofs
            if (!p.getSettings().getChoiceSettings()
                    .equals(newNode.proof().getSettings().getChoiceSettings())) {
                continue;
            }
            Set<Node> checkedNodes = new HashSet<>();
            Queue<Node> nodesToCheck = p.closedGoals().stream().map(goal -> {
                // first, find the initial node in this branch
                Node n = goal.node();
                if (n.parent() != null
                        && n.parent().getAppliedRuleApp().rule() == CloseAfterMerge.INSTANCE) {
                    // cannot reference this kind of branch
                    return null;
                }
                return n;
            }).filter(Objects::nonNull).collect(Collectors.toCollection(ArrayDeque::new));
            var depTracker = p.lookup(DependencyTracker.class);
            AnalysisResults results = null;
            // only try to get analysis results if it is a pure proof
            if (depTracker != null && p.closedGoals().stream()
                    .noneMatch(x -> x.node().lookup(ClosedBy.class) != null)) {
                try {
                    results = depTracker.analyze(true, false);
                } catch (Exception ignored) {
                    // if the analysis for some reason fails, we simply proceed as usual
                }
            }
            while (!nodesToCheck.isEmpty()) {
                // for each node, check that the sequent in the reference is
                // a subset of the new sequent
                Node n = nodesToCheck.remove();
                if (checkedNodes.contains(n) || !n.isClosed()) {
                    continue;
                }
                checkedNodes.add(n);

                // find the first node in the branch
                while (n.parent() != null && n.parent().childrenCount() == 1) {
                    n = n.parent();
                }
                if (n.parent() != null) {
                    nodesToCheck.add(n.parent());
                }
                Sequent seq = n.sequent();
                if (results != null) {
                    seq = results.reduceSequent(n);
                }
                Semisequent ante = seq.antecedent();
                Semisequent succ = seq.succedent();
                Semisequent anteNew = newNode.sequent().antecedent();
                Semisequent succNew = newNode.sequent().succedent();
                if (!containedIn(anteNew, ante) || !containedIn(succNew, succ)) {
                    continue;
                }
                Set<Node> toSkip = new HashSet<>();
                if (results != null) {
                    // computed skipped nodes by iterating through all nodes
                    AnalysisResults finalResults = results;
                    n.subtreeIterator().forEachRemaining(x -> {
                        if (!finalResults.usefulSteps.contains(x)) {
                            toSkip.add(x);
                        }
                    });
                }
                return new ClosedBy(p, n, toSkip);
            }
        }
        return null;
    }

    /**
     * Check whether all formulas in {@code subset} are conatined in {@code superset}.
     *
     * @param superset Semisequent supposed to contain {@code subset}
     * @param subset Semisequent supposed to be in {@code superset}
     * @return whether all formulas are present
     */
    private static boolean containedIn(Semisequent superset, Semisequent subset) {
        for (SequentFormula sf : subset) {
            boolean found = false;
            for (SequentFormula sf2 : superset) {
                if ((Object) sf instanceof SequentFormula that
                        && EqualityModuloProofIrrelevancy.equalsModProofIrrelevancy(sf2, that)) {
                    found = true;
                    break;
                }
            }
            if (!found) {
                return false;
            }
        }
        return true;
    }

    /**
     * Check whether a node is suitable for closing by reference.
     * This is not the case if it contains any terms influenced by external factors:
     * Java blocks or program methods (query terms).
     *
     * @param node the node to check
     * @return whether it can be closed by reference
     */
    public static boolean suitableForCloseByReference(Node node) {
        ProgramMethodFinder f = new ProgramMethodFinder();
        Sequent seq = node.sequent();
        for (int i = 1; i <= seq.size(); i++) {
            JTerm term = (JTerm) seq.getFormulaByNr(i).formula();
            // first, check for a java block
            if (term.containsJavaBlockRecursive()) {
                // not suitable for caching
                return false;
            }
            // then, check for program methods
            // (may expand differently depending on Java code associated with proofs)
            term.execPreOrder(f);
            if (f.getFoundProgramMethod()) {
                return false;
            }
        }
        return true;
    }
}
