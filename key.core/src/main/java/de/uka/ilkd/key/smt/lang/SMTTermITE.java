/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.smt.lang;

import java.util.LinkedList;
import java.util.List;
import java.util.Objects;


public class SMTTermITE extends SMTTerm {

    SMTTerm condition;

    SMTTerm trueCase;

    SMTTerm falseCase;

    private static final String ITE_STRING = "ite";



    public SMTTermITE(SMTTerm condition, SMTTerm trueCase, SMTTerm falseCase) {
        super();
        this.condition = condition;

        if (condition.sort() != SMTSort.BOOL) {
            throw new IllegalArgumentException(
                "ite condition must be of type bool, but got: " + condition);
        }
        this.trueCase = trueCase;
        this.falseCase = falseCase;
    }

    @Override
    public boolean occurs(SMTTermVariable a) {
        return condition.occurs(a) || trueCase.occurs(a) || falseCase.occurs(a);
    }

    @Override
    public boolean occurs(String id) {
        return condition.occurs(id) || trueCase.occurs(id) || falseCase.occurs(id);
    }

    @Override
    public SMTSort sort() {
        return trueCase.sort();
    }

    @Override
    public SMTTerm substitute(SMTTermVariable a, SMTTerm b) {
        return new SMTTermITE(condition.substitute(a, b), trueCase.substitute(a, b),
            falseCase.substitute(a, b));
    }

    @Override
    public SMTTerm substitute(SMTTerm a, SMTTerm b) {
        return new SMTTermITE(condition.substitute(a, b), trueCase.substitute(a, b),
            falseCase.substitute(a, b));
    }

    @Override
    public SMTTerm replace(SMTTermCall a, SMTTerm b) {
        return new SMTTermITE(condition.replace(a, b), trueCase.replace(a, b),
            falseCase.replace(a, b));
    }

    @Override
    public SMTTerm instantiate(SMTTermVariable a, SMTTerm b) {
        return new SMTTermITE(condition.instantiate(a, b), trueCase.instantiate(a, b),
            falseCase.instantiate(a, b));
    }

    @Override
    public SMTTerm copy() {
        return new SMTTermITE(condition.copy(), trueCase.copy(), falseCase.copy());
    }

    @Override
    public String toString(int nestPos) {
        String tab = " ".repeat(Math.max(0, nestPos));
        return tab + "(" + ITE_STRING + "\n" + condition.toString(nestPos + 1) + "\n"
            + trueCase.toString(nestPos + 1) + "\n" + falseCase.toString(nestPos + 1) + "\n" + tab
            + ")";
    }

    @Override
    public String toString() {
        return toString(0);
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) {
            return true;
        }
        if (!(o instanceof SMTTermITE)) {
            return false;
        }
        SMTTermITE that = (SMTTermITE) o;
        return condition.equals(that.condition) && trueCase.equals(that.trueCase)
                && falseCase.equals(that.falseCase);
    }

    @Override
    public int hashCode() {
        return Objects.hash(condition, trueCase, falseCase);
    }

    /**
     * @return the condition
     */
    public SMTTerm getCondition() {
        return condition;
    }

    /**
     * @return the trueCase
     */
    public SMTTerm getTrueCase() {
        return trueCase;
    }

    /**
     * @return the falseCase
     */
    public SMTTerm getFalseCase() {
        return falseCase;
    }

    /**
     * @param condition the condition to set
     */
    public void setCondition(SMTTerm condition) {
        this.condition = condition;
    }

    /**
     * @param trueCase the trueCase to set
     */
    public void setTrueCase(SMTTerm trueCase) {
        this.trueCase = trueCase;
    }

    /**
     * @param falseCase the falseCase to set
     */
    public void setFalseCase(SMTTerm falseCase) {
        this.falseCase = falseCase;
    }

    /** {@inheritDoc} */
    @Override
    public List<SMTTermVariable> getQuantVars() {
        List<SMTTermVariable> vars = new LinkedList<>();
        vars.addAll(condition.getQuantVars());
        vars.addAll(trueCase.getQuantVars());
        vars.addAll(falseCase.getQuantVars());
        return vars;
    }
}
