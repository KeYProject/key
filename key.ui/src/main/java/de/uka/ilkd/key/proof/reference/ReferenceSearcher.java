package de.uka.ilkd.key.proof.reference;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.logic.Semisequent;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.ProgramMethod;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;

import java.util.Optional;

public class ReferenceSearcher {
    private ReferenceSearcher() {

    }

    public static ClosedBy findPreviousProof(KeYMediator mediator, Node newNode) {
        // TODO:
        // - disallow closing by reference to merged branch
        // - once the other proof is closed, copy the steps into the new proof
        // - when saving the new proof, copy the steps

        // first verify that the new node does not contain any terms that depend on external
        // influences
        ProgramMethodFinder f = new ProgramMethodFinder();
        Sequent seq = newNode.sequent();
        for (int i = 1; i <= seq.size(); i++) {
            Term term = seq.getFormulabyNr(i).formula();
            if (term.containsJavaBlockRecursive()) {
                return null;
            }
            term.execPreOrder(f);
            if (f.getFoundProgramMethod()) {
                return null;
            }
        }
        var proofs = mediator.getCurrentlyOpenedProofs();
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
                while (n.parent() != null && n.parent().childrenCount() == 1) {
                    n = n.parent();
                }
                return n;
            }).filter(node -> {
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
}
