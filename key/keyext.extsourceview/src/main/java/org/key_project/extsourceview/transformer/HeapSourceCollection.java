package org.key_project.extsourceview.transformer;

import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.Node;

import java.util.HashMap;
import java.util.HashSet;

public class HeapSourceCollection {

    private final HashMap<Integer, Integer> data = new HashMap<>();
    private final HashSet<Term> processed = new HashSet<>();

    public HeapSourceCollection() {  }

    public void collect(Node startNode) throws InternTransformException {
        for (var node = startNode; node != null; node = node.parent()) {
            collect(node.sequent());
        }
    }

    private void collect(Sequent sequent) throws InternTransformException {
        for (var sf : sequent.antecedent().asList()) {
            collect(sf.formula());
        }
        for (var sf : sequent.succedent().asList()) {
            collect(sf.formula());
        }
    }

    private void collect(Term term) throws InternTransformException {
        if (processed.contains(term)) {
            return;
        }
        processed.add(term);

        if (term.op().name().toString().endsWith("::select") && term.arity() == 3) {
            var updates = MovingPositioner.listHeapUpdates(term.sub(0));
            for (var upd : updates) {
                if (upd.Origin != null && upd.Origin.hasFile()) {
                    if (upd.Origin.LineStart == upd.Origin.LineEnd) {
                        data.compute(upd.Origin.LineEnd, (k,v) -> (v == null) ? 1 : v+1);
                    }/* else {
                        data.compute(upd.Origin.LineStart, (k,v) -> (v == null) ? 1 : v+1);
                        data.compute(upd.Origin.LineEnd, (k,v) -> (v == null) ? 1 : v+1);
                    }*/
                }
            }
        }

        for (var subterm : term.subs()) {
            collect(subterm);
        }
    }

    public int getHeapCount(int line) {
        return data.getOrDefault(line, 0);
    }
}
