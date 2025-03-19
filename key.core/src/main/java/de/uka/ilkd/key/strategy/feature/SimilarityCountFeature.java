/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.feature;

import java.util.LinkedList;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.ldt.LocSetLDT;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.strategy.NumberRuleAppCost;
import de.uka.ilkd.key.strategy.RuleAppCost;
import de.uka.ilkd.key.strategy.termProjection.ProjectionToTerm;


/**
 * A feature that computes the depth of the find-position of a taclet (top-level
 * positions have depth zero or if not a find taclet)
 *
 * TODO: eliminate this class and use term features instead
 */
public class SimilarityCountFeature implements Feature {

    private ProjectionToTerm first;
    private ProjectionToTerm second;

    public static Feature create(ProjectionToTerm first, ProjectionToTerm second) {
        return new SimilarityCountFeature(first, second);
    }

    private SimilarityCountFeature(ProjectionToTerm first, ProjectionToTerm second) {
        this.first = first;
        this.second = second;
    }

    public RuleAppCost computeCost(RuleApp app, PosInOccurrence pos, Goal goal) {
        Term fst = first.toTerm(app, pos, goal);
        Term snd = second.toTerm(app, pos, goal);

        LocSetLDT locsetLDT = goal.proof().getServices().getTypeConverter().getLocSetLDT();

        Term subFst = null;
        Term subSnd = null;
        int penalty = 0;

        int countSetMinusFst = 0;
        int countSetMinusSnd = 0;
        while (fst.op() == locsetLDT.getSetMinus() || snd.op() == locsetLDT.getSetMinus()) {

            if (fst.op() == locsetLDT.getSetMinus()) {
                subFst = fst.sub(1);
                fst = fst.sub(0);
                countSetMinusFst++;
            } else {
                subFst = null;
            }
            if (snd.op() == locsetLDT.getSetMinus()) {
                subSnd = snd.sub(1);
                snd = snd.sub(0);
                countSetMinusSnd++;
            } else {
                subSnd = null;
            }

            if ((subFst != null || subSnd != null)) {
                if ((subFst != null && subSnd == null) || (subSnd != null && subFst == null) ||
                        !subFst.equalsModRenaming(subSnd)) {
                    penalty += 1 + (countSetMinusFst - countSetMinusSnd);
                }
            }
        }

        int count = 0;

        LinkedList<Term> toCompute = new LinkedList<>();

        toCompute.add(fst);

        while (!toCompute.isEmpty()) {
            final Term next = toCompute.pop();
            if (next.op() == locsetLDT.getUnion()) {
                toCompute.add(next.sub(0));
                toCompute.add(next.sub(1));
            } else {
                count += weightLocSets(next, snd, app, pos, goal);
            }
        }

        return NumberRuleAppCost.create(count - penalty > 0 ? count - penalty : 0);
    }

    private int weightLocSets(Term fst, Term snd,
            final RuleApp p_app, final PosInOccurrence p_pos, final Goal p_goal) {
        Services services = p_goal.proof().getServices();
        LocSetLDT locSetLDT = services.getTypeConverter().getLocSetLDT();
        HeapLDT heapLDT = services.getTypeConverter().getHeapLDT();
        TermBuilder tb = services.getTermBuilder();

        int count = 0;

        if (fst.op() != snd.op()) {
            if (fst.op() == locSetLDT.getMatrixRange() &&
                    snd.op() == locSetLDT.getSingleton()) {
                Term singletonObject = snd.sub(0);
                Term singletonField = snd.sub(1);
                Term currentHeap, array, index;
                if (singletonField.op() == heapLDT.getArr()) {
                    if (heapLDT.isSelectOp(singletonObject.op()) &&
                            singletonObject.sub(2).op() == heapLDT.getArr()) {
                        currentHeap = singletonObject.sub(0);
                        array = singletonObject.sub(1);
                        index = singletonObject.sub(2).sub(0);
                        Term orgSnd = snd;
                        snd =
                            tb.matrixRange(currentHeap, array, index, index, singletonField.sub(0),
                                singletonField.sub(0));
                    }
                }
            }
        }

        if (fst.op() == snd.op() && fst.op() == locSetLDT.getMatrixRange()) {
            final Term matrixSucc = snd;

            Feature startRowIncl = PolynomialValuesCmpFeature.leq((app, pos, goal) -> fst.sub(2),
                (app, pos, goal) -> matrixSucc.sub(2));
            Feature endRowIncl =
                PolynomialValuesCmpFeature.leq((app, pos, goal) -> matrixSucc.sub(3),
                    (app, pos, goal) -> fst.sub(3));

            Feature startColIncl = PolynomialValuesCmpFeature.leq((app, pos, goal) -> fst.sub(4),
                (app, pos, goal) -> matrixSucc.sub(4));
            Feature endColIncl =
                PolynomialValuesCmpFeature.leq((app, pos, goal) -> matrixSucc.sub(5),
                    (app, pos, goal) -> fst.sub(5));

            Feature crossColumns1 =
                PolynomialValuesCmpFeature.leq((app, pos, goal) -> matrixSucc.sub(4),
                    (app, pos, goal) -> fst.sub(5));
            Feature crossColumns2 = PolynomialValuesCmpFeature.leq((app, pos, goal) -> fst.sub(4),
                (app, pos, goal) -> matrixSucc.sub(5));

            RuleAppCost costs[] = new RuleAppCost[4];
            costs[0] = startRowIncl.computeCost(p_app, p_pos, p_goal);
            costs[1] = endRowIncl.computeCost(p_app, p_pos, p_goal);
            costs[2] = startColIncl.computeCost(p_app, p_pos, p_goal);
            costs[3] = endColIncl.computeCost(p_app, p_pos, p_goal);
            for (RuleAppCost cost : costs) {
                if (cost.equals(NumberRuleAppCost.getZeroCost())) {
                    count += 10;
                }
            }

            RuleAppCost crossCosts[] = new RuleAppCost[2];
            crossCosts[0] = crossColumns1.computeCost(p_app, p_pos, p_goal);
            crossCosts[1] = crossColumns2.computeCost(p_app, p_pos, p_goal);
            for (RuleAppCost cost : crossCosts) {
                if (cost.equals(NumberRuleAppCost.getZeroCost())) {
                    count += 5;
                }
            }
            for (int idx = 2; idx < 6; idx++) {
                if (fst.sub(idx).op() == services.getTypeConverter().getIntegerLDT()
                        .getNumberSymbol()) {
                    count += 2;
                }
            }
        } else if (fst.op() == snd.op() && fst.op() == locSetLDT.getArrayRange()) {
            final Term arraySucc = snd;
            Feature startRowIncl = PolynomialValuesCmpFeature.leq((app, pos, goal) -> fst.sub(1),
                (app, pos, goal) -> arraySucc.sub(1));
            Feature endRowIncl =
                PolynomialValuesCmpFeature.leq((app, pos, goal) -> arraySucc.sub(2),
                    (app, pos, goal) -> fst.sub(2));
            Feature crossRow1 = PolynomialValuesCmpFeature.leq((app, pos, goal) -> arraySucc.sub(1),
                (app, pos, goal) -> fst.sub(2));
            Feature crossRow2 = PolynomialValuesCmpFeature.leq((app, pos, goal) -> fst.sub(1),
                (app, pos, goal) -> arraySucc.sub(2));

            RuleAppCost costs[] = new RuleAppCost[2];
            costs[0] = startRowIncl.computeCost(p_app, p_pos, p_goal);
            costs[1] = endRowIncl.computeCost(p_app, p_pos, p_goal);
            for (RuleAppCost cost : costs) {
                if (cost.equals(NumberRuleAppCost.getZeroCost())) {
                    count += 10;
                }
            }
            RuleAppCost crossCosts[] = new RuleAppCost[2];
            crossCosts[0] = crossRow1.computeCost(p_app, p_pos, p_goal);
            crossCosts[1] = crossRow2.computeCost(p_app, p_pos, p_goal);
            for (RuleAppCost cost : crossCosts) {
                if (cost.equals(NumberRuleAppCost.getZeroCost())) {
                    count += 5;
                }
            }
            for (int idx = 1; idx < 3; idx++) {
                if (fst.sub(idx).op() == services.getTypeConverter().getIntegerLDT()
                        .getNumberSymbol()) {
                    count += 2;
                }
            }
        } else {
            if (fst.arity() != snd.arity()) {
                return 0;
            }
            for (int i = 0; i < fst.arity(); i++) {
                if (fst.sub(i).equalsModRenaming(snd.sub(i))) {
                    count += 10 * (6 / fst.arity());
                }
            }
        }
        return count;
    }

}
