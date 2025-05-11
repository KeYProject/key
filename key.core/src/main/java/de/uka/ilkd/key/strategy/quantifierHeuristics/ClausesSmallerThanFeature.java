/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.quantifierHeuristics;

import de.uka.ilkd.key.ldt.IntegerLDT;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.strategy.feature.Feature;
import de.uka.ilkd.key.strategy.feature.MutableState;
import de.uka.ilkd.key.strategy.feature.SmallerThanFeature;
import de.uka.ilkd.key.strategy.termProjection.ProjectionToTerm;
import org.jspecify.annotations.NonNull;

/**
 * Ordering used to sort the clauses in a quantified formula. This ordering should only be applied
 * if at least one of the two clauses contains more than one literal (otherwise, use
 * <code>LiteralsSmallerThanFeature</code>).
 */
public class ClausesSmallerThanFeature extends SmallerThanFeature {

    private final ProjectionToTerm left, right;

    private final QuanEliminationAnalyser quanAnalyser = new QuanEliminationAnalyser();

    private final @NonNull LiteralsSmallerThanFeature litComparator;

    private ClausesSmallerThanFeature(ProjectionToTerm left, ProjectionToTerm right,
            IntegerLDT numbers) {
        this.left = left;
        this.right = right;
        this.litComparator =
            (LiteralsSmallerThanFeature) LiteralsSmallerThanFeature.create(left, right, numbers);
    }

    public static @NonNull Feature create(ProjectionToTerm left, ProjectionToTerm right,
                                          IntegerLDT numbers) {
        return new ClausesSmallerThanFeature(left, right, numbers);
    }

    protected boolean filter(TacletApp app, PosInOccurrence pos, Goal goal, MutableState mState) {
        final Term leftTerm = left.toTerm(app, pos, goal, mState);
        final Term rightTerm = right.toTerm(app, pos, goal, mState);

        final ClauseCollector m1 = new ClauseCollector();
        m1.collect(leftTerm);
        final ClauseCollector m2 = new ClauseCollector();
        m2.collect(rightTerm);

        return lessThan(m1.getResult(), m2.getResult(), pos, goal);
    }

    /**
     * this overwrites the method of <code>SmallerThanFeature</code>
     */
    @Override
    protected boolean lessThan(@NonNull Term t1, @NonNull Term t2, @NonNull PosInOccurrence focus, Goal goal) {

        final int t1Def = quanAnalyser.eliminableDefinition(t1, focus);
        final int t2Def = quanAnalyser.eliminableDefinition(t2, focus);

        if (t1Def > t2Def) {
            return true;
        }
        if (t1Def < t2Def) {
            return false;
        }

        if (t1.op() == Junctor.OR) {
            if (t2.op() == Junctor.OR) {
                return super.lessThan(t1, t2, focus, goal);
            } else {
                return false;
            }
        } else {
            if (t2.op() == Junctor.OR) {
                return true;
            } else {
                return litComparator.compareTerms(t1, t2, focus, goal);
            }
        }
    }

    private static class ClauseCollector extends Collector {
        protected void collect(@NonNull Term te) {
            final Operator op = te.op();
            if (op == Junctor.AND) {
                collect(te.sub(0));
                collect(te.sub(1));
            } else {
                addTerm(te);
            }
        }
    }

}
