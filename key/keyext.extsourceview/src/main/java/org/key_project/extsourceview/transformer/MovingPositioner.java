package org.key_project.extsourceview.transformer;

import de.uka.ilkd.key.java.PositionInfo;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;

import java.net.URI;
import java.util.ArrayList;
import java.util.List;
import java.util.Optional;
import java.util.stream.Collectors;

/**
 * Implements the 'Heap' Positioning strategy for InsertionTerms
 * The terms get written in the lines where the contained heaps originate from
 */
public class MovingPositioner extends InsPositionProvider{
    private final URI fileUri;

    private final HeapSourceCollection heapSources;

    public MovingPositioner(URI fileUri, Services svc, Proof proof, Node node, HeapSourceCollection hsc) {
        super(svc, proof, node);

        this.fileUri = fileUri;
        this.heapSources = hsc;
    }

    public static List<HeapReference> listHeaps(Term t, boolean distinct) throws InternTransformException {
        var result = new ArrayList<HeapReference>();

        if (t.op().name().toString().endsWith("::select") && t.arity() == 3) {
            var updates = listHeapUpdates(t.sub(0));
            result.add(new HeapReference(updates));
        }

        for (var sub: t.subs()) {
            result.addAll(listHeaps(sub, false));
        }

        if (distinct) {
            var dist = new ArrayList<HeapReference>();
            for (var h: result) {
                if (dist.stream().noneMatch(p -> p.heapEquals(h))) {
                    dist.add(h);
                }
            }
            result = dist;
        }

        return result;
    }

    public static List<HeapReference.HeapUpdate> listHeapUpdates(Term t) throws InternTransformException {

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

    public Optional<Integer> GetTermHeapPosition(Term t, InsertionType itype) {
        try {
            if (t.op().name().toString().endsWith("::select") && t.arity() == 3) {

                var heaps = listHeaps(t, false).stream().filter(p -> p.getLineNumber().isPresent()).collect(Collectors.toList());

                return heaps.stream().map(p -> p.getLineNumber().orElse(0)).max(Integer::compare);
            } else {
                return Optional.empty();
            }
        } catch (InternTransformException e) {
            return Optional.empty();
        }
    }

    private int getActiveStatementPosition(URI fileUri) throws InternTransformException, TransformException {

        for (Node cur = this.node; cur != null; cur = cur.parent()) {
            SourceElement activeStatement = cur.getNodeInfo().getActiveStatement();
            if (activeStatement != null) {
                PositionInfo pi = activeStatement.getPositionInfo();
                if (pi == PositionInfo.UNDEFINED) continue;
                if (pi.getURI() == PositionInfo.UNKNOWN_URI) continue;

                return pi.getStartPosition().getLine() + 1;
            }
        }

        // fallback (?) use method-start directly

        return getMethodPositionMap().getStartPosition().getLine() + 1;
    }

    @Override
    public InsertionPosition getPosition(InsertionTerm iterm) throws InternTransformException, TransformException {
        return getPosition(iterm.Term, iterm.Type);
    }

    private InsertionPosition getPosition(Term term, InsertionType itype) throws InternTransformException, TransformException {
        switch (itype) {
            case ASSERT:
            case ASSERT_ERROR:
                return getPositionAssert(term);
            case ASSUME:
            case ASSUME_ERROR:
                return getPositionAssume(term);
            case ASSIGNABLE:
                return getPositionAssignable(term);
            default:
                throw new InternTransformException("Unknown InsertionTerm.Type: " + itype);
        }
    }

    private InsertionPosition getPositionAssume(Term term) throws InternTransformException, TransformException {
        var methodPosition = getMethodPositionMap();

        var heaps = listHeaps(term, false).stream().filter(p -> p.getLineNumber().isPresent()).collect(Collectors.toList());

        var symbExecPos = getActiveStatementPosition(fileUri);

        // ======== [1] Start position is at method-start

        var position = methodPosition.getStartPosition().getLine() + 1;

        // ======== [2.1] move forward to position of last contained heap-update

        if (heaps.size() > 0) {

            int heapLine = heaps.stream().map(p -> p.getLineNumber().orElse(0)).max(Integer::compare).orElse(0);

            position = heapLine + 1;
        }

        // ======== [2.2] (if there are _no_ heaps - move forward to (before) symb exec)

        //TODO keep this??
        if (heaps.size() == 0 && !containsObserverFunc(term)) {
            position = symbExecPos-1;
        }

        // ======== [3] move further forward, but only until we reach the symb exec position
        //              and not over lines that introduce heap updates.
        //              Also: IObserverFunction do not get moved.

        if (!containsObserverFunc(term)) {
            while (true) {
                if (position + 1 >= symbExecPos) break;

                if (canMoveAssumeAfterLine(position)) {
                    position++;
                } else {
                    break;
                }
            }
        }

        var indent = getLineIndent(fileUri, position);
        return new InsertionPosition(position, indent);
    }

    private boolean containsObserverFunc(Term term) {
        if (term.op() instanceof IObserverFunction) {
            return true;
        }
        for (int i = 0; i < term.arity(); i++) {
            if (containsObserverFunc(term.sub(i))) {
                return true;
            }
        }
        return false;
    }

    private InsertionPosition getPositionAssert(Term term) throws InternTransformException, TransformException {
        var methodPosition = getMethodPositionMap();

        var heaps = listHeaps(term, false).stream().filter(p -> p.getLineNumber().isPresent()).collect(Collectors.toList());

        // ======== [1] Start position is at method-end

        var position = methodPosition.getEndPosition().getLine();

        // ======== [2] Move backwards, until we reach symb-execution or a heap update

        var symbExecPos = getActiveStatementPosition(fileUri);

        while (true) {

            if (position <= symbExecPos) break;

            if (canMoveAssertBeforeLine(position-1)) {
                position--;
            } else {
                break;
            }

        }

        var indent = getLineIndent(fileUri, position);
        return new InsertionPosition(position, indent);
    }

    private InsertionPosition getPositionAssignable(Term term) throws InternTransformException, TransformException {
        var methodPosition = getMethodPositionMap();

        // assignable (for now) simply at method-end

        var line = methodPosition.getEndPosition().getLine();

        var indent = getLineIndent(fileUri, line);
        return new InsertionPosition(line, indent);
    }

    private boolean canMoveAssumeAfterLine(int line) {
        return heapSources.getHeapCount(line) == 0;
    }

    private boolean canMoveAssertBeforeLine(int line) {
        return heapSources.getHeapCount(line) == 0;
    }

    @Override
    public Integer getOldPos() throws TransformException {
        return getMethodPositionMap().getStartPosition().getLine() + 1;
    }
}
