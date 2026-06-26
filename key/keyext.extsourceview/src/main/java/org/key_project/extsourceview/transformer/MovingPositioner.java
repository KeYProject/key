package org.key_project.extsourceview.transformer;

import de.uka.ilkd.key.java.PositionInfo;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.expression.Assignment;
import de.uka.ilkd.key.java.visitor.JavaASTVisitor;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import org.key_project.extsourceview.Utils;

import java.io.IOException;
import java.net.URI;
import java.util.*;
import java.util.stream.Collectors;

/**
 * Implements the 'Heap' Positioning strategy for InsertionTerms
 * The terms get written in the lines where the contained heaps originate from
 */
public class MovingPositioner extends InsPositionProvider {
    private final URI fileUri;

    private final HeapSourceCollection heapSources;
    private final List<SourceElement> statements;

    /** maps each program variable to the first line where it is written */
    private final Map<String, Integer> localVarMap = new HashMap<>();

    private class WrittenAndDeclaredPVLineCollector extends JavaASTVisitor {
        public WrittenAndDeclaredPVLineCollector(ProgramElement root, Services services) {
            super(root, services);
        }

        @Override
        protected void doDefaultAction(SourceElement node) {
            if (node instanceof Assignment) {
                ProgramElement lhs = ((Assignment) node).getChildAt(0);
                if (lhs instanceof ProgramVariable) {
                    ProgramVariable pv = (ProgramVariable) lhs;
                    if (!pv.isMember()) {
                        int l = node.getStartPosition().getLine();
                        String varName = pv.name().toString();
                        if (!localVarMap.containsKey(varName)) {
                            localVarMap.put(varName, l);
                        } else {
                            int o = localVarMap.get(varName);
                            if (o > l) {
                                localVarMap.put(varName, l);
                            }
                        }
                    }
                }
            } /*else if (node instanceof VariableSpecification) {
                VariableSpecification vs = (VariableSpecification) node;
                ProgramVariable pv = (ProgramVariable) vs.getProgramVariable();
                if (!pv.isMember()) {
//                    declaredPVs = declaredPVs.add(pv);
                    String varName = pv.name().toString();
                    int l = node.getStartPosition().getLine();
                    if (!localVarMap.containsKey(varName)) {
                        localVarMap.put(varName, l);
                    } else {
                        int o = localVarMap.get(varName);
                        if (o > l) {
                            localVarMap.put(varName, l);
                        }
                    }
                }
            }*/
        }
    }

    public MovingPositioner(URI fileUri, Services svc, Proof proof, Node node, HeapSourceCollection hsc) {
        super(svc, proof, node);

        statements = createStatementList();

        for (SourceElement statement : statements) {
            /*ImmutableSet<ProgramVariable> getLocalIns = MiscTools.getLocalIns(
                (ProgramElement) statement, svc);
            ImmutableSet<ProgramVariable> getLocalOuts = MiscTools.getLocalOuts(
                (ProgramElement) statement, svc);*/

            WrittenAndDeclaredPVLineCollector wpvc = new WrittenAndDeclaredPVLineCollector(
                (ProgramElement) statement, svc);
            wpvc.start();
        }

        this.fileUri = fileUri;
        this.heapSources = hsc;
    }

    public static List<HeapReference> listHeaps(Sequent s, Term t, boolean distinct) throws InternTransformException, TransformException {
        var result = new ArrayList<HeapReference>();

        if (t.op().name().toString().equals("store") && t.arity() == 4) {
            var updates = listHeapUpdates(s, t);
            result.add(new HeapReference(updates));
        } else if (t.op().name().toString().equals("anon") && t.arity() == 3) {
            var updates = listHeapUpdates(s, t);
            result.add(new HeapReference(updates));
        } else if (t.op().name().toString().endsWith("::select") && t.arity() == 3) {
            var updates = listHeapUpdates(s, t.sub(0));
            result.add(new HeapReference(updates));
        } else {
            for (var sub: t.subs()) {
                result.addAll(listHeaps(s, sub, false));
            }
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

    public static List<HeapReference.HeapUpdate> listHeapUpdates(Sequent s, Term t) throws InternTransformException, TransformException {

        if (!t.sort().name().toString().equals("Heap")) {
            throw new InternTransformException("Not a heap");
        }

        var result = new ArrayList<HeapReference.HeapUpdate>();

        if (t.op().name().toString().equals("store")) {
            result.add(HeapReference.newStoreUpdate(t));
            result.addAll(listHeapUpdates(s, t.sub(0)));
            return result;
        } else if (t.op().name().toString().equals("anon")) {
            result.add(HeapReference.newAnonUpdate(t));
            result.addAll(listHeapUpdates(s, t.sub(0)));
            return result;
        } else if (t.op() instanceof LocationVariable && t.op().name().toString().startsWith("heap")) {
            result.add(HeapReference.newHeap(t));
            return result;
        } else if (t.op() instanceof Function && t.arity() == 0) {

            for (var ss : s.antecedent()) {
                var f = ss.formula();
                if (f.op() == Equality.EQUALS && f.arity() == 2 && f.sub(0).sort().name().toString().equals("Heap") && f.sub(0).op().name().toString().equals(t.op().name().toString())) {
                    result.add(HeapReference.newIndirect(t));
                    result.addAll(listHeapUpdates(s, f.sub(1)));
                    return result;
                }
                if (f.op() == Equality.EQUALS && f.arity() == 2 && f.sub(1).sort().name().toString().equals("Heap") && f.sub(1).op().name().toString().equals(t.op().name().toString())) {
                    result.add(HeapReference.newIndirect(t));
                    result.addAll(listHeapUpdates(s, f.sub(0)));
                    return result;
                }
            }

            for (var ss : s.succedent()) {
                var fnot = ss.formula();
                if (fnot.op() == Junctor.NOT && fnot.arity() == 1) {
                    var f = fnot.sub(0);
                    if (f.op() == Equality.EQUALS && f.arity() == 2 && f.sub(0).sort().name().toString().equals("Heap") && f.sub(0).op().name().toString().equals(t.op().name().toString())) {
                        result.add(HeapReference.newIndirect(t));
                        result.addAll(listHeapUpdates(s, f.sub(1)));
                        return result;
                    }
                    if (f.op() == Equality.EQUALS && f.arity() == 2 && f.sub(1).sort().name().toString().equals("Heap") && f.sub(1).op().name().toString().equals(t.op().name().toString())) {
                        result.add(HeapReference.newIndirect(t));
                        result.addAll(listHeapUpdates(s, f.sub(0)));
                        return result;
                    }
                }
            }

            //throw new TransformException("failed to find definition for Function '" + t.op().name().toString() + "'");

            result.add(HeapReference.newHeap(t));
            return result;

        } else {
            throw new TransformException("Unknown heap op", t.op().getClass().getSimpleName()+" -> '" + t.op().name().toString() + "'");
        }
    }

    public Optional<Integer> GetTermHeapPosition(Sequent s, Term t, InsertionType itype) {
        try {
            var methodPosition = getMethodPositionMap();

            if (t.op().name().toString().endsWith("::select") && t.arity() == 3) {

                var heaps = listHeaps(s, t, false).stream().filter(p -> p.getLineNumber(methodPosition).isPresent()).collect(Collectors.toList());

                return heaps.stream().map(p -> p.getLineNumber(methodPosition).orElse(0)).max(Integer::compare);
            } else {
                return Optional.empty();
            }
        } catch (InternTransformException | TransformException e) {
            return Optional.empty();
        }
    }

    private List<SourceElement> createStatementList() {

        List<SourceElement> statements = new ArrayList<>();
        for (Node cur = this.node; cur != null; cur = cur.parent()) {
            SourceElement activeStatement = cur.getNodeInfo().getActiveStatement();
            if (activeStatement != null) {
                var pi = activeStatement.getPositionInfo();
                if (pi.startEndValid()) {
                    // filter out multiline (hack)
                    var start = pi.getStartPosition();
                    var end = pi.getEndPosition();
                    if (end.getLine() - start.getLine() == 0) {
                        statements.add(activeStatement);
                    }
                }
            }
        }

        return statements;
    }

    /**
     * Search from the current node upwards until an node with an active statement is found.
     * Return its line number, or the start of the method body, if none is found.
     * @param fileUri
     * @return
     * @throws InternTransformException
     * @throws TransformException
     */
    private int getActiveStatementPosition(URI fileUri) throws InternTransformException, TransformException {

        for (Node cur = this.node; cur != null; cur = cur.parent()) {
            SourceElement activeStatement = cur.getNodeInfo().getActiveStatement();
            if (activeStatement != null) {
                PositionInfo pi = activeStatement.getPositionInfo();
                if (pi == PositionInfo.UNDEFINED) continue;
                if (pi.getURI() == PositionInfo.UNKNOWN_URI) continue;
                if (!fileUri.equals(pi.getURI())) continue;

                return pi.getStartPosition().getLine() + 1;
            }
        }

        // fallback (?) use method-start directly

        return getMethodPositionMap().getStartPosition().getLine() + 1;
    }

    @Override
    public InsertionPosition getPosition(Sequent s, InsertionTerm iterm) throws InternTransformException, TransformException {
        return getPosition(s, iterm.Term, iterm.Type);
    }

    private InsertionPosition getPosition(Sequent s, Term term, InsertionType itype) throws InternTransformException, TransformException {
        switch (itype) {
            case ASSERT:
            case ASSERT_ERROR:
                return getPositionAssert(s, term);
            case ASSUME:
            case ASSUME_ERROR:
                return getPositionAssume(s, term);
            case ASSIGNABLE:
                return getPositionAssignable(term);
            default:
                throw new InternTransformException("Unknown InsertionTerm.Type: " + itype);
        }
    }

    private InsertionPosition getPositionAssume(Sequent s, Term term) throws InternTransformException, TransformException {
        var methodPosition = getMethodPositionMap();

        var heaps = listHeaps(s, term, false).stream().filter(p -> p.getLineNumber(methodPosition).isPresent()).collect(Collectors.toList());

        var symbExecPos = getActiveStatementPosition(fileUri);

        // ======== [1] Start position is at method-start

        var position = methodPosition.getStartPosition().getLine()/* + 1*/;

        // ======== [2.1] move forward to position of last contained heap-update

        if (heaps.size() > 0) {

            int heapLine = heaps.stream().map(p -> p.getLineNumber(methodPosition).orElse(0)).max(Integer::compare).orElse(0);

            position = heapLine + 1;
        }

        // ======== [2.2] (if there are _no_ heaps - move forward to (before) symb exec)

        /*if (heaps.size() == 0 && !containsObserverFunc(term) && symbExecPos > 0) {
            position = symbExecPos-1;
        }*/

        // ======== [3] move further forward, but only until we reach the symb exec position
        //              and not over lines that introduce heap updates.
        //              Also: IObserverFunction do not get moved.

        if (!containsObserverFunc(term)) {
            while (true) {
                if (position  >= symbExecPos) {
                    // done: we reached the position of the symb. ex.
                    break;
                }

                //if (canMoveAssumeAfterLine(position)) {
                    if (canMoveLocalVar(term, position)) {
                        position++;
                    } else {
                        System.out.println();
                        break;
                    }
                /*} else {
                    System.out.println();
                    break;
                }*/
            }
        }

        var indent = getLineIndent(fileUri, position);
        return new InsertionPosition(position, position-1, indent);
    }

    private boolean canMoveLocalVar(Term term, int position) {
        // TODO: we somehow need to remove everything before the position the original assumptions comes from (e.g. loop invariant, post condition)
        List<String> locVarNamesCanditates = collectLocVarNames(term);
//        System.out.println("Term: " + term + "\nlocVarNamesCanditates: " + locVarNamesCanditates);
        for (String locVarName : locVarNamesCanditates) {
            if (localVarMap.containsKey(locVarName)) {
                // localVarMap holds the maximum line number we can move this term to
                int varLine = localVarMap.get(locVarName);
                if (varLine > position) {
                    // not yet reached the maximum
                    return true;
                }
            }
        }
        return false;
    }

    private String existsProgVar(String name) {
        int i = name.lastIndexOf('_');
        if (i < 0) {
            return null;
        } else {
            String noPrefix = name.substring(0, i);
            for (var f : node.getLocalProgVars()) {
                if (f.name().toString().equals(noPrefix)) {
                    return noPrefix;
                }
            }
        }
        return null;
    }

    private List<String> collectLocVarNames(Term term) {
        List<String> result = new ArrayList<>();

        if (term.op() instanceof Function) {
            String noPrefix = existsProgVar(term.op().name().toString());
            if (noPrefix != null) {
                //Function f = (Function) term.op();
                result.add(noPrefix);
                return result;
            }
        }
        if (!term.subs().isEmpty()) {
            for (Term sub : term.subs()) {
                result.addAll(collectLocVarNames(sub));
            }
        }
        return result;
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

    private InsertionPosition getPositionAssert(Sequent s, Term term) throws InternTransformException, TransformException {
        var methodPosition = getMethodPositionMap();

        var heaps = listHeaps(s, term, false).stream().filter(p -> p.getLineNumber(methodPosition).isPresent()).collect(Collectors.toList());

        var symbExecPos = getActiveStatementPosition(fileUri);

        // ======== [1] Start position is at method-end

        var position = methodPosition.getEndPosition().getLine();

        // ======== [2] Move backwards, until we reach symb-execution or a heap update

        while (true) {

            if (position <= symbExecPos) break;

            if (canMoveAssertBeforeLine(position-1)) {
                position--;
            } else {
                break;
            }

        }

        // ======== [3.1] If position == symbExecPos && branch == 'Pre (%s)'
        //                we decrement the position by one, because we want the <pre> asserts to be before the method call
        //                This can be removed once the symb exec no longer shows the method as executed in the pre-branch

        if (position == symbExecPos && isBranch(node, "Pre")) {
            position--;
        }

        // ======== [3.2] If position == symbExecPos && stmt == 'return'
        //                we decrement the position by one, because we want the asserts to be before the return call
        //                This only works if our returns are primitives (aka return $variable), but this is a stated precondition

        if (position == symbExecPos && isReturnStmt(position-1)) {
            position--;
        }

        var indent = getLineIndent(fileUri, position);
        return new InsertionPosition(position, position-1, indent);
    }

    private boolean isReturnStmt(int position) throws InternTransformException {
        try {
            return Utils.getLines(fileUri, position, position).trim().toLowerCase().startsWith("return");
        } catch (IOException e) {
            throw new InternTransformException(e.getMessage());
        }
    }

    private boolean isBranch(Node n, String branchPrefix) {
        var lbl = n.getNodeInfo().getBranchLabel();
        if (lbl != null && lbl.startsWith(branchPrefix)) return true;
        var parent = n.parent();
        if (parent == null) return false;
        return isBranch(parent, branchPrefix);
    }

    private InsertionPosition getPositionAssignable(Term term) throws InternTransformException, TransformException {
        var methodPosition = getMethodPositionMap();

        // assignable (for now) simply at method-end

        var line = methodPosition.getEndPosition().getLine();

        var indent = getLineIndent(fileUri, line);
        return new InsertionPosition(line, line, indent);
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

    @Override
    public Integer getLoopStartPos() throws TransformException, InternTransformException {
        //TODO this is kinda hacky, we need a better way to find the (heap) position of the current loop
        try {

            var symbExecPos = getActiveStatementPosition(fileUri);
            for (int i = symbExecPos; i > 0; i--) {
                if (heapSources.getHeapCount(i) > 0 && Utils.getLines(fileUri, i, i).contains("while")) {
                    return i;
                }
            }
        } catch (IOException e) {
            throw new InternTransformException(e.getMessage());
        }
        return null;
    }

    @Override
    public boolean heapPosAreEqual(int p1, int p2) {
        return heapSources.normalizeHeapPos(p1) == heapSources.normalizeHeapPos(p2);
    }
}
