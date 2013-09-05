package de.uka.ilkd.key.rule.conditions;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.FormulaSV;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.VariableConditionAdapter;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

public class SubFormulaCondition extends VariableConditionAdapter {

    private final FormulaSV a;
    private final boolean negated;

    public SubFormulaCondition(FormulaSV a, boolean negated) {
        this.a = a;
        this.negated = negated;
    }

    @Override
    public boolean check(SchemaVariable var, SVSubstitute instCandidate,
                         SVInstantiations instMap, Services services) {        
        if (!(var instanceof FormulaSV) || (FormulaSV)var != this.a) {
            return false;
        }
        Term tInst = (Term) instMap.getInstantiation((FormulaSV)a);
        if (tInst.arity() == 0) {
            return negated;
        } else {
            for (Term sub: tInst.subs()) {
                if (sub.sort() == Sort.FORMULA) {
                    return !negated;
                }
            }
            return negated;
        }
    }

    @Override
    public String toString() {
        return (negated ? "\\not":"") + "\\hasSubFormulas (" + a + ")";
    }
}