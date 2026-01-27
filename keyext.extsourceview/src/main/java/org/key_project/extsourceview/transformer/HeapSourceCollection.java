package org.key_project.extsourceview.transformer;

import org.key_project.prover.sequent.Sequent;
import org.key_project.logic.Term;
import de.uka.ilkd.key.proof.Node;

import java.util.HashMap;
import java.util.HashSet;

public class HeapSourceCollection {

    private final Sequent sequent;

    private final HashMap<Integer, Integer> data = new HashMap<>();
    private final HashSet<Term> processed = new HashSet<>();

    public HeapSourceCollection(Sequent seq) {
        this.sequent = seq;
    }

    public void collect(Node startNode) throws InternTransformException, TransformException {
        for (var node = startNode; node != null; node = node.parent()) {
            collect(node.sequent());
        }
    }

    private void collect(Sequent sequent) throws InternTransformException, TransformException {
        for (var sf : sequent.antecedent().asList()) {
            collect(sf.formula());
        }
        for (var sf : sequent.succedent().asList()) {
            collect(sf.formula());
        }
    }

    private void collect(Term term) throws InternTransformException, TransformException {
        if (processed.contains(term)) {
            return;
        }
        processed.add(term);

        if (term.op().name().toString().endsWith("::select") && term.arity() == 3) {
            var updates = MovingPositioner.listHeapUpdates(sequent, term.sub(0));
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

    public int normalizeHeapPos(int pos) {

        int lastHeapLine = 1;

        for (int line = 1; line <= pos; line++) {

            int heapCount = getHeapCount(line);

            if (heapCount>0) lastHeapLine=line;

        }

        return lastHeapLine;
    }
}
