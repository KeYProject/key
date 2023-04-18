package de.uka.ilkd.key.proof.reference;

import java.util.Optional;
import javax.swing.*;

import de.uka.ilkd.key.logic.Semisequent;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.merge.CloseAfterMerge;

/**
 * Utility class for proof caching.
 *
 * @author Arne Keller
 */
public class ReferenceSearcher {
    private ReferenceSearcher() {

    }

    /**
     * Try to find a closed branch in another proof that is equivalent to the <code>newNode</code>.
     *
     * @param previousProofs old proofs
     * @param newNode new node (must be an open goal)
     * @return a reference (or null, if none found)
     */
    public static ClosedBy findPreviousProof(DefaultListModel<Proof> previousProofs, Node newNode) {
        // first verify that the new node does not contain any terms that depend on external
        // influences
        if (!suitableForCloseByReference(newNode)) {
            return null;
        }
        DefaultListModel<Proof> proofs = previousProofs;
        for (int i = 0; i < proofs.size(); i++) {
            Proof p = proofs.get(i);
            // only search in compatible proofs
            if (!p.getSettings().getChoiceSettings()
                    .equals(newNode.proof().getSettings().getChoiceSettings())) {
                continue;
            }
            Optional<Node> match = p.closedGoals().stream().map(goal -> {
                // first, find the initial node in this branch
                Node n = goal.node();
                if (n.parent() != null
                        && n.parent().getAppliedRuleApp().rule() == CloseAfterMerge.INSTANCE) {
                    // cannot reference this kind of branch
                    return null;
                }
                while (n.parent() != null && n.parent().childrenCount() == 1) {
                    n = n.parent();
                }
                return n;
            }).filter(node -> {
                if (node == null) {
                    return false;
                }
                // check that all formulas are also present in the new proof
                Semisequent ante = node.sequent().antecedent();
                Semisequent succ = node.sequent().succedent();
                Semisequent anteNew = newNode.sequent().antecedent();
                Semisequent succNew = newNode.sequent().succedent();
                if (!containedIn(anteNew, ante) || !containedIn(succNew, succ)) {
                    return false;
                }
                return true;
            }).findAny();
            if (match.isPresent()) {
                return new ClosedBy(p, match.get());
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
                if (sf2.equalsModProofIrrelevancy(sf)) {
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
            Term term = seq.getFormulabyNr(i).formula();
            if (term.containsJavaBlockRecursive()) {
                return false;
            }
            term.execPreOrder(f);
            if (f.getFoundProgramMethod()) {
                return false;
            }
        }
        return true;
    }
}
