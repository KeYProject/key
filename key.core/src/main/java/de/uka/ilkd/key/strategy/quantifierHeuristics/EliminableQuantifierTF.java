/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.quantifierHeuristics;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.op.Quantifier;
import de.uka.ilkd.key.strategy.feature.MutableState;
import de.uka.ilkd.key.strategy.termfeature.BinaryTermFeature;
import de.uka.ilkd.key.strategy.termfeature.TermFeature;

import org.key_project.logic.Term;

public class EliminableQuantifierTF extends BinaryTermFeature {

    public static final TermFeature INSTANCE = new EliminableQuantifierTF();

    private final QuanEliminationAnalyser quanAnalyser = new QuanEliminationAnalyser();

    private EliminableQuantifierTF() {}

    @Override
    protected boolean filter(Term term, MutableState mState, Services services) {
        final var op = term.op();
        assert op == Quantifier.ALL || op == Quantifier.EX;

        Term matrix = term;
        do {
            matrix = matrix.sub(0);
        } while (matrix.op() == term.op());

        if (matrix.op() == Quantifier.ALL || matrix.op() == Quantifier.EX) {
            return false;
        }

        final QuantifiableVariable var = (QuantifiableVariable) term.varsBoundHere(0).last();

        return quanAnalyser.isEliminableVariableAllPaths(var, matrix, op == Quantifier.EX);
    }

}
