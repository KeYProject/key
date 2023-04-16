package de.uka.ilkd.key.strategy.termfeature;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Operator;

/**
 * Term feature for checking whether the top operator of a term is identical to a given one
 */
public class OperatorTF extends BinaryTermFeature {

    private final Operator op;

    private OperatorTF(Operator op) {
        this.op = op;
    }

    public static TermFeature create(Operator op) {
        return new OperatorTF(op);
    }

    protected boolean filter(Term term, Services services) {
        return op == term.op();
    }
}
