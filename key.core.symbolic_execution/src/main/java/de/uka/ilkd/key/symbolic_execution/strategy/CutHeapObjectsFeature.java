/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.symbolic_execution.strategy;

import java.util.Iterator;

import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.op.Equality;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.strategy.termProjection.SVInstantiationProjection;

import org.key_project.logic.Name;
import org.key_project.prover.proof.ProofGoal;
import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.sequent.Sequent;
import org.key_project.prover.sequent.SequentFormula;
import org.key_project.prover.strategy.costbased.MutableState;
import org.key_project.prover.strategy.costbased.feature.BinaryFeature;

import org.jspecify.annotations.NonNull;

/**
 * <p>
 * This {@link BinaryFeature} checks if a cut with an equality for an alias check should be done or
 * not.
 * </p>
 * <p>
 * This means the cut is only applied if the cut formula is not an equality or if it is not a
 * negated formula or if the (negated) equality is not contained as top term
 * ({@link SequentFormula}) in the {@link Sequent} ignoring the order of the equality children.
 * </p>
 *
 * @author Martin Hentschel
 */
public class CutHeapObjectsFeature extends BinaryFeature {
    /**
     * {@inheritDoc}
     */
    @Override
    protected <Goal extends ProofGoal<@NonNull Goal>> boolean filter(RuleApp app,
            PosInOccurrence pos, Goal goal, MutableState mState) {
        JTerm cutFormula =
            SVInstantiationProjection.create(new Name("cutFormula"), false).toTerm(app, pos,
                (de.uka.ilkd.key.proof.Goal) goal,
                mState);
        if (cutFormula != null) {
            if (cutFormula.op() == Junctor.NOT) {
                cutFormula = cutFormula.sub(0);
            }
            if (cutFormula.op() == Equality.EQUALS) {
                JTerm cutFormulaC0 = cutFormula.sub(0);
                JTerm cutFormulaC1 = cutFormula.sub(1);
                boolean contains = false;
                Iterator<SequentFormula> iter = goal.sequent().iterator();
                while (!contains && iter.hasNext()) {
                    var formula = iter.next().formula();
                    if (formula.op() == Junctor.NOT) {
                        formula = formula.sub(0);
                    }
                    if (formula.op() == Equality.EQUALS) {
                        // Check equality ignore order of equality sub terms
                        if (cutFormulaC0.equals(formula.sub(0))) {
                            contains = cutFormulaC1.equals(formula.sub(1));
                        } else {
                            contains = cutFormulaC0.equals(formula.sub(1))
                                    && cutFormulaC1.equals(formula.sub(0));
                        }
                    }
                }
                return !contains; // Perform cut only if equality is not already part of the
                                  // sequent's top formulas
            } else {
                return true; // Unknown cut type
            }
        } else {
            return false; // Cut without cutFormula is not possible
        }
    }
}
