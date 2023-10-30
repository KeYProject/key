/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.feature;

import de.uka.ilkd.key.ldt.IntegerLDT;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.strategy.termProjection.ProjectionToTerm;


/**
 * Feature that returns zero iff each variable/atom of one monomial is smaller than all variables of
 * a second monomial
 */
public class AtomsSmallerThanFeature extends AbstractMonomialSmallerThanFeature {

    private final ProjectionToTerm left, right;
    private final Function Z;

    private AtomsSmallerThanFeature(ProjectionToTerm left, ProjectionToTerm right,
            IntegerLDT numbers) {
        super(numbers);
        this.left = left;
        this.right = right;
        this.Z = numbers.getNumberSymbol();
    }


    public static Feature create(ProjectionToTerm left, ProjectionToTerm right,
            IntegerLDT numbers) {
        return new AtomsSmallerThanFeature(left, right, numbers);
    }

    protected boolean filter(TacletApp app, PosInOccurrence pos, Goal goal) {
        final boolean res = lessThan(collectAtoms(left.toTerm(app, pos, goal)),
            collectAtoms(right.toTerm(app, pos, goal)), pos, goal);
        return res;
    }

    /**
     * this overwrites the method of <code>SmallerThanFeature</code>
     */
    @Override
    protected boolean lessThan(Term t1, Term t2, PosInOccurrence focus, Goal goal) {
        if (t1.op() == Z) {
            if (t2.op() != Z) {
                return true;
            }
            return super.lessThan(t1, t2, focus, goal);
        } else {
            if (t2.op() == Z) {
                return false;
            }
        }

        final int v = introductionTime(t2.op(), goal) - introductionTime(t1.op(), goal);
        if (v < 0) {
            return true;
        }
        if (v > 0) {
            return false;
        }

        return super.lessThan(t1, t2, focus, goal);
    }
}
