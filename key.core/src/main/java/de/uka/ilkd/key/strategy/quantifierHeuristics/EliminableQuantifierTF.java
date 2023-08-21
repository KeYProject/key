/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.quantifierHeuristics;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.op.Quantifier;
import de.uka.ilkd.key.strategy.termfeature.BinaryTermFeature;
import de.uka.ilkd.key.strategy.termfeature.TermFeature;

public class EliminableQuantifierTF extends BinaryTermFeature {

    public static final TermFeature INSTANCE = new EliminableQuantifierTF();

    private final QuanEliminationAnalyser quanAnalyser = new QuanEliminationAnalyser();

    private EliminableQuantifierTF() {}

    protected boolean filter(Term term, Services services) {
        final Operator op = term.op();
        assert op == Quantifier.ALL || op == Quantifier.EX;

        Term matrix = term;
        do {
            matrix = matrix.sub(0);
        } while (matrix.op() == term.op());

        if (matrix.op() == Quantifier.ALL || matrix.op() == Quantifier.EX) {
            return false;
        }

        final QuantifiableVariable var = term.varsBoundHere(0).last();

        return quanAnalyser.isEliminableVariableAllPaths(var, matrix, op == Quantifier.EX);
    }

}
