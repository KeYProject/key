package de.uka.ilkd.key.logic;

import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.Set;

import de.uka.ilkd.key.logic.op.ElementaryUpdate;
import de.uka.ilkd.key.logic.op.Operator;

/**
 * Collects all operators occurring in the traversed term.
 */
public class OpCollector extends DefaultVisitor {
    /** the found operators */
    private HashSet<Operator> ops;

    /** creates the Op collector */
    public OpCollector() {
        ops = new LinkedHashSet<Operator>();
    }

    public void visit(Term t) {
        ops.add(t.op());
        if (t.op() instanceof ElementaryUpdate) {
            ops.add(((ElementaryUpdate) t.op()).lhs());
        }
    }

    public boolean contains(Operator op) {
        return ops.contains(op);
    }

    public Set<Operator> ops() {
        return ops;
    }
}
