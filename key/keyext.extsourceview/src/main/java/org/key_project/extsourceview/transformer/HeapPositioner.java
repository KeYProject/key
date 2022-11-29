package org.key_project.extsourceview.transformer;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;

import java.net.URI;
import java.util.ArrayList;
import java.util.List;
import java.util.stream.Collectors;

public class HeapPositioner extends InsPositionProvider{
    private final boolean continueOnError;

    private final MethodPositioner fallback;

    public HeapPositioner(Services svc, Proof proof, Node node, boolean continueOnError) {
        super(svc, proof, node);

        this.continueOnError = continueOnError;

        this.fallback = new MethodPositioner(svc, proof, node);
    }

    public List<HeapReference> listHeaps(Term t) throws InternTransformException {
        var result = new ArrayList<HeapReference>();

        if (t.op().name().toString().endsWith("::select") && t.arity() == 3) {
            var updates = listHeapUpdates(t.sub(0));
            result.add(new HeapReference(updates));
        }

        for (var sub: t.subs()) {
            result.addAll(listHeaps(sub));
        }

        return result;
    }

    public List<HeapReference.HeapUpdate> listHeapUpdates(Term t) throws InternTransformException {

        if (!t.sort().name().toString().equals("Heap")) {
            throw new InternTransformException("Not a heap");
        }

        var result = new ArrayList<HeapReference.HeapUpdate>();

        if (t.op().name().toString().equals("store")) {
            result.addAll(listHeapUpdates(t.sub(0)));
            result.add(HeapReference.newStoreUpdate(t));
            return result;
        } else if (t.op().name().toString().equals("anon")) {
            result.addAll(listHeapUpdates(t.sub(0)));
            result.add(HeapReference.newAnonUpdate(t));
            return result;
        } else if (t.op() instanceof LocationVariable) {
            result.add(HeapReference.newHeap(t));
            return result;
        } else if (t.op() instanceof Function && t.arity() == 0) {
            result.add(HeapReference.newHeap(t));
            return result;
        } else {
            throw new InternTransformException("unknown heap op");
        }
    }

    @Override
    public InsertionPosition getPosition(URI fileUri, InsertionTerm iterm) throws InternTransformException, TransformException {
        var methodPosition = getMethodPositionMap();

        if (iterm.Type == InsertionType.ASSIGNABLE) {
            var line = methodPosition.getEndPosition().getLine();
            var indent = getLineIndent(fileUri, line);
            return new InsertionPosition(line, indent);
        }

        var heaps = listHeaps(iterm.Term).stream().filter(p -> p.getLineNumber().isPresent()).collect(Collectors.toList());

        if (heaps.size() == 0) {
            return fallback.getPosition(fileUri, iterm);
        }

        var line = heaps.stream().map(p -> p.getLineNumber().orElse(0)).max(Integer::compare).orElse(-1);

        if (line == -1) {
            return fallback.getPosition(fileUri, iterm);
        }

        line += 1; // should be _after_ this line (that changed the heap)

        var indent = getLineIndent(fileUri, line);


        return new InsertionPosition(line, indent);
    }
}
