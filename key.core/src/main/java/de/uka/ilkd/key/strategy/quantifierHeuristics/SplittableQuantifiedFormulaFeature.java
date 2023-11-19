/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.quantifierHeuristics;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.op.Quantifier;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.strategy.feature.BinaryFeature;
import de.uka.ilkd.key.strategy.feature.Feature;
import de.uka.ilkd.key.strategy.feature.MutableState;

import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableSet;

public class SplittableQuantifiedFormulaFeature extends BinaryFeature {

    private SplittableQuantifiedFormulaFeature() {}

    public static final Feature INSTANCE = new SplittableQuantifiedFormulaFeature();

    protected boolean filter(RuleApp app, PosInOccurrence pos, Goal goal, MutableState mState) {
        assert pos != null : "Feature is only applicable to rules with find";

        final Analyser analyser = new Analyser();
        if (!analyser.analyse(pos.sequentFormula().formula())) {
            return false;
        }

        if (analyser.binOp == Junctor.AND) {
            return TriggerUtils.intersect(
                TriggerUtils.intersect(analyser.left.freeVars(), analyser.right.freeVars()),
                analyser.existentialVars).size() == 0;
        } else if (analyser.binOp == Junctor.OR) {
            return TriggerUtils.intersect(analyser.left.freeVars(), analyser.right.freeVars())
                    .union(analyser.existentialVars).size() == analyser.existentialVars.size();
        }

        return false;
    }

    private static class Analyser {
        public ImmutableSet<QuantifiableVariable> existentialVars =
            DefaultImmutableSet.nil();
        public Operator binOp;
        public Term left, right;

        public boolean analyse(Term formula) {
            final Operator op = formula.op();

            if (op == Quantifier.ALL) {
                // might be that a variable is bound more than once
                existentialVars = existentialVars.remove(formula.varsBoundHere(0).last());
                return analyse(formula.sub(0));
            }

            if (op == Quantifier.EX) {
                existentialVars = existentialVars.add(formula.varsBoundHere(0).last());
                return analyse(formula.sub(0));
            }

            if (op == Junctor.AND || op == Junctor.OR) {
                binOp = op;
                left = formula.sub(0);
                right = formula.sub(1);
                return true;
            }

            return false;
        }
    }
}
