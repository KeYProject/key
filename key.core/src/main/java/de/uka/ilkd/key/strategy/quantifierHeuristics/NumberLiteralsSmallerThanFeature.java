/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.quantifierHeuristics;

import java.math.BigInteger;

import de.uka.ilkd.key.ldt.IntegerLDT;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.strategy.feature.Feature;
import de.uka.ilkd.key.strategy.feature.MutableState;
import de.uka.ilkd.key.strategy.feature.SmallerThanFeature;
import de.uka.ilkd.key.strategy.termProjection.ProjectionToTerm;

public class NumberLiteralsSmallerThanFeature extends SmallerThanFeature {

    private final ProjectionToTerm left, right;
    private final IntegerLDT numbers;

    private final QuanEliminationAnalyser quanAnalyser =
        new QuanEliminationAnalyser();


    private NumberLiteralsSmallerThanFeature(ProjectionToTerm left,
            ProjectionToTerm right,
            IntegerLDT numbers) {
        this.left = left;
        this.right = right;
        this.numbers = numbers;
    }

    public static Feature create(ProjectionToTerm left,
            ProjectionToTerm right,
            IntegerLDT numbers) {
        return new NumberLiteralsSmallerThanFeature(left, right, numbers);
    }

    protected boolean filter(TacletApp app, PosInOccurrence pos, Goal goal, MutableState mState) {
        final IntegerLDT intLDT = goal.proof().getServices().getTypeConverter().getIntegerLDT();
        final Operator Z = intLDT.getNumberSymbol();

        final Term leftTerm = left.toTerm(app, pos, goal, mState);
        final Term rightTerm = right.toTerm(app, pos, goal, mState);

        if (leftTerm.op() != Z || rightTerm.op() != Z) {
            return false;
        }

        return compareTerms(leftTerm, rightTerm, intLDT);
    }

    protected boolean compareTerms(Term leftTerm, Term rightTerm,
            IntegerLDT intLDT) {
        BigInteger left = toBigInt(leftTerm, intLDT);
        BigInteger right = toBigInt(rightTerm, intLDT);
        return left.compareTo(right) == -1;
    }

    private BigInteger toBigInt(Term literal, IntegerLDT intLDT) {
        if (literal.op() != intLDT.getNumberSymbol()) {
            throw new RuntimeException(literal + " is no number.");
        }
        BigInteger result = BigInteger.ZERO;
        Term current = literal.sub(0);
        boolean negate = false;
        while (current.op() == intLDT.getNegativeNumberSign()) {
            negate = negate ? false : true;
            current = current.sub(0);
        }
        while (current.op() != intLDT.getNumberTerminator()) {
            final BigInteger digit = new BigInteger(current.op().name().toString());
            result = digit.add(result.multiply(BigInteger.valueOf(10)));
            current = current.sub(0);
        }
        return negate ? result.negate() : result;
    }
}
