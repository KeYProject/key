package de.uka.ilkd.key.rule.conditions;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.op.TermSV;
import de.uka.ilkd.key.rule.VariableConditionAdapter;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

public class AtomicCondition extends VariableConditionAdapter {

    private final TermSV t;
    private final boolean negated;

    public AtomicCondition(TermSV t, boolean negated) {
        this.t = t;
        this.negated = negated;
    }

    @Override
    public boolean check(SchemaVariable var,
                         SVSubstitute instCandidate,
                         SVInstantiations instMap,
                         Services services) {
        if (!(var instanceof TermSV) || (TermSV)var != this.t) {
            return true;
        }
        Term tInst = (Term) instMap.getInstantiation(t);
        boolean atomic = (tInst.arity() == 0);
        return negated ? !atomic : atomic;
    }

    @Override
    public String toString() {
        return (negated ? "\\not":"") + "\\isAtomic (" + t + ")";
    }
}