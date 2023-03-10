package de.uka.ilkd.key.proof.reference;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.logic.Semisequent;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.ProgramMethod;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;

public class ReferenceSearcher {
    private ReferenceSearcher() {

    }

    public static ClosedBy findPreviousProof(KeYMediator mediator, Node newNode) {
        // TODO:
        // - disallow closing by reference to merged branch
        // - once the other proof is closed, copy the steps into the new proof
        // - when saving the new proof, copy the steps
        // - compare sequents using the new equality infrastructure in the slicing branch

        // first verify that the new node does not contains any terms that depend on external
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
            // only search closed proofs, for now
            // (it would be enough to only search in closed branches)
            if (!p.closed()) {
                continue;
            }
            if (!p.getSettings().getChoiceSettings()
                    .equals(newNode.proof().getSettings().getChoiceSettings())) {
                continue;
            }
            // iterate over all branching nodes of the proof
            Node match = p.findAny(node -> {
                if (node.parent() == null || node.parent().childrenCount() < 2) {
                    return false;
                }
                System.out.println("checking node " + node.serialNr());
                // check that all formulas are also present in the new proof
                Semisequent ante = node.sequent().antecedent();
                Semisequent succ = node.sequent().succedent();
                Semisequent anteNew = newNode.sequent().antecedent();
                Semisequent succNew = newNode.sequent().succedent();
                if (!containedIn(anteNew, ante) || !containedIn(succNew, succ)) {
                    return false;
                }
                return true;
            });
            int id = match != null ? match.serialNr() : 0;
            System.out.println("closable by " + id);
            if (match != null) {
                return new ClosedBy(p, match);
            }
        }
        return null;
    }

    private static boolean containedIn(Semisequent superset, Semisequent subset) {
        for (SequentFormula sf : subset) {
            String sfString = sf.toString();
            boolean found = false;
            for (SequentFormula sf2 : superset) {
                if (sf2.toString().equals(sfString)) {
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
