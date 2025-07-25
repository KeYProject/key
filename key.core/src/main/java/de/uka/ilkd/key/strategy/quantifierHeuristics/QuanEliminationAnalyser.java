/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.quantifierHeuristics;

import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.op.Equality;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.op.Quantifier;

import org.key_project.logic.Term;
import org.key_project.logic.op.QuantifiableVariable;
import org.key_project.prover.sequent.PosInOccurrence;

public class QuanEliminationAnalyser {

    /**
     *
     * @param definition
     * @return the distance to the quantifier that can be eliminated; <code>Integer.MAX_VALUE</code>
     *         if the subformula is not an eliminable definition
     */
    public int eliminableDefinition(Term definition,
            PosInOccurrence envPIO) {
        final PosInOccurrence matrixPIO = walkUpMatrix(envPIO);
        final Term matrix = matrixPIO.subTerm();

        if (matrixPIO.isTopLevel()) {
            return Integer.MAX_VALUE;
        }

        PosInOccurrence quantPIO = matrixPIO.up();
        Term quantTerm = quantPIO.subTerm();
        final boolean ex;
        if (quantTerm.op() == Quantifier.EX) {
            ex = true;
        } else if (quantTerm.op() == Quantifier.ALL) {
            ex = false;
        } else {
            return Integer.MAX_VALUE;
        }

        if (!isDefinitionCandidate(definition, envPIO.subTerm(), ex)) {
            return Integer.MAX_VALUE;
        }

        int distance = 0;
        while (true) {
            final QuantifiableVariable var = quantTerm.varsBoundHere(0).last();

            if (isDefinition(definition, var, ex)
                    && isEliminableVariableSomePaths(var, matrix, ex)) {
                return distance;
            }

            if (quantPIO.isTopLevel()) {
                return Integer.MAX_VALUE;
            }
            quantPIO = quantPIO.up();
            quantTerm = quantPIO.subTerm();

            if (quantTerm.op() != (ex ? Quantifier.EX : Quantifier.ALL)) {
                return Integer.MAX_VALUE;
            }

            ++distance;
        }
    }

    private boolean isDefinitionCandidate(Term t, Term env, boolean ex) {
        if (!hasDefinitionShape(t, ex)) {
            return false;
        }
        return !ex || !isBelowOr(t, env);
    }

    private boolean isBelowOr(Term t, Term env) {
        final var envOp = env.op();
        if (envOp == Junctor.OR && (env.sub(0) == t || env.sub(1) == t)) {
            return true;
        }
        if (envOp == Junctor.OR || envOp == Junctor.AND) {
            return isBelowOr(t, env.sub(0)) || isBelowOr(t, env.sub(1));
        }
        return false;
    }

    private boolean hasDefinitionShape(Term t, boolean ex) {
        for (QuantifiableVariable quantifiableVariable : t.freeVars()) {
            if (isDefinition(t, quantifiableVariable, ex)) {
                return true;
            }
        }
        return false;
    }

    private PosInOccurrence walkUpMatrix(
            PosInOccurrence pio) {
        while (!pio.isTopLevel()) {
            final PosInOccurrence parent = pio.up();
            final var parentOp = parent.subTerm().op();
            if (parentOp != Junctor.AND && parentOp != Junctor.OR) {
                return pio;
            }
            pio = parent;
        }
        return pio;
    }

    /**
     * The variable <code>var</code> is either eliminable or does not occur on all
     * conjunctive/disjunctive paths through <code>matrix</code> (depending on whether
     * <code>ex</code> is true/false)
     */
    public boolean isEliminableVariableSomePaths(QuantifiableVariable var, Term matrix,
            boolean ex) {
        if (!((JTerm) matrix).freeVars()
                .contains(var)) {
            return true;
        }

        final var op = matrix.op();

        if (op == (ex ? Junctor.OR : Junctor.AND)) {
            return isEliminableVariableSomePaths(var, matrix.sub(0), ex)
                    && isEliminableVariableSomePaths(var, matrix.sub(1), ex);
        } else if (op == (ex ? Junctor.AND : Junctor.OR)) {
            return isEliminableVariableAllPaths(var, matrix.sub(0), ex)
                    || isEliminableVariableAllPaths(var, matrix.sub(1), ex)
                    || (isEliminableVariableSomePaths(var, matrix.sub(0), ex)
                            && isEliminableVariableSomePaths(var, matrix.sub(1), ex));
        }

        if (ex) {
            return isDefiningEquationEx(matrix, var);
        } else {
            return isDefiningEquationAll(matrix, var);
        }
    }

    /**
     * The variable <code>var</code> is eliminable on all conjunctive/disjunctive paths through
     * <code>matrix</code> (depending on whether <code>ex</code> is true/false)
     */
    public boolean isEliminableVariableAllPaths(QuantifiableVariable var, Term matrix, boolean ex) {
        final var op = matrix.op();

        if (op == (ex ? Junctor.OR : Junctor.AND)) {
            return isEliminableVariableAllPaths(var, matrix.sub(0), ex)
                    && isEliminableVariableAllPaths(var, matrix.sub(1), ex);
        } else if (op == (ex ? Junctor.AND : Junctor.OR)) {
            return isEliminableVariableAllPaths(var, matrix.sub(0), ex)
                    || isEliminableVariableAllPaths(var, matrix.sub(1), ex);
        }

        if (ex) {
            return isDefiningEquationEx(matrix, var);
        } else {
            return isDefiningEquationAll(matrix, var);
        }
    }

    private boolean isDefinition(Term t, QuantifiableVariable var, boolean ex) {
        if (ex) {
            return isDefinitionEx(t, var);
        } else {
            return isDefiningEquationAll(t, var);
        }
    }

    private boolean isDefinitionEx(Term t, QuantifiableVariable var) {
        if (t.op() == Junctor.OR) {
            return isDefinitionEx(t.sub(0), var) && isDefinitionEx(t.sub(1), var);
        }
        return isDefiningEquationEx(t, var);
    }

    private boolean isDefiningEquationAll(Term t, QuantifiableVariable var) {
        if (t.op() != Junctor.NOT) {
            return false;
        }
        return isDefiningEquation(t.sub(0), var);
    }

    private boolean isDefiningEquationEx(Term t, QuantifiableVariable var) {
        return isDefiningEquation(t, var);
    }

    private boolean isDefiningEquation(Term t, QuantifiableVariable var) {
        if (t.op() != Equality.EQUALS) {
            return false;
        }
        final var left = (JTerm) t.sub(0);
        final var right = (JTerm) t.sub(1);
        final var leftOp = left.op();
        final var rightOp = right.op();
        return leftOp == var
                && !right.freeVars().contains(var)
                || rightOp == var && !left.freeVars()
                        .contains(var);
    }

}
