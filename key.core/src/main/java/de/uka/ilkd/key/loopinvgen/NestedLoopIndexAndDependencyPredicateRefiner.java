/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.loopinvgen;

import java.util.HashSet;
import java.util.Set;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Equality;
import de.uka.ilkd.key.logic.op.JFunction;

import org.key_project.util.collection.Pair;

/**
 * Refinement of the predicates describing the loop index and the dependency predicates
 */
public class NestedLoopIndexAndDependencyPredicateRefiner extends PredicateRefiner {

    private final Term indexOuter;
    private final Term arrOuter;
    private final Term indexInner;
    private final Term arrInner;
    private final int itrNumber;

    private Set<Term> depPredicates;
    private Set<Term> compPredicates;

    public NestedLoopIndexAndDependencyPredicateRefiner(Sequent sequent, Set<Term> depPredList,
            Set<Term> compPredList, Term arrOuter, Term arrInner,
            Term indexOuter, Term indexInner, int iteration, Services services) {
        super(sequent, services);
        this.depPredicates = depPredList;
        this.compPredicates = compPredList;
        this.indexOuter = indexOuter;
        this.arrOuter = arrOuter;
        this.indexInner = indexInner;
        this.arrInner = arrInner;
        this.itrNumber = iteration;

    }

    @Override
    public Pair<Set<Term>, Set<Term>> refine() {
        Set<Term> unProvenDepPreds = new HashSet<>();
        for (Term pred : depPredicates) {
            // System.out.println("abel + 1 " + pred);
            if (!sequentImpliesPredicate(pred)) {
                // System.out.println("not implied by the seq: " + pred);
                unProvenDepPreds.add(pred);
            }
        }
        depPredicates.removeAll(unProvenDepPreds);
        Set<Term> weakenedDepPreds = new HashSet<>();
        for (Term un : unProvenDepPreds) {
            weakenedDepPreds.addAll(weakeningDependencePredicates(un));
        }

        for (Term w : weakenedDepPreds) {
            boolean weakerPredicateIsSubsumed = false;
            // System.out.println("Weak pred: " + w);
            for (Term dp : depPredicates) { // to not loose precision here, the refinement needs to
                                            // have the property that if dp is removed at some point
                                            // t1 then there will be a time tn which adds w again
                                            // (or something that implies it)
                if (predicateImpliedByPredicate(w, dp)) {
                    // System.out.println("IMPLIED " + w + " by " + dp);
                    weakerPredicateIsSubsumed = true;
                    break;
                }
            }
            if (!weakerPredicateIsSubsumed && !depPredicates.contains(w)) {
                // System.out.println("Proving Dep Pred: " + w);
                if (sequentImpliesPredicate(w)) {
                    depPredicates.add(w);
                }
            }
        }
        // System.out.println("DEP PREDS: " + depPredicates);
        // -------------------------------------
        Set<Term> unProvenCompPreds = new HashSet<>();
        for (Term pred : compPredicates) {
            // System.out.println("Proving Comp Pred: " + pred);
            if (!sequentImpliesPredicate(pred)) {
                unProvenCompPreds.add(pred);
            }
        }
        compPredicates.removeAll(unProvenCompPreds);
        Set<Term> weakenedCompPreds = new HashSet<>();
        for (Term un : unProvenCompPreds) {
            // System.out.println("Weakening unproven: " + un);
            weakenedCompPreds.addAll(weakeningComparisonPredicates(un));
        }

        for (Term w : weakenedCompPreds) {
            // System.out.println("Proving Weakened Comp Pred: " + w);
            if (sequentImpliesPredicate(w)) {
                compPredicates.add(w);
            }
        }
        return new Pair<>(depPredicates, compPredicates);
    }

    // tries to prove that dp2 -> dp1, i.e. noX(l2) -> noY(l1)
    private boolean predicateImpliedByPredicate(Term dp1, Term dp2) {
        if (dp1.op() == dp2.op() && sProof.proofSubSet(dp1.sub(0), dp2.sub(0))) {
            return true;
        } else if (dp2.op().equals(depLDT.getNoR())) {
            if (dp1.op().equals(depLDT.getNoRaW()) || dp1.op().equals(depLDT.getNoWaR())) {
                return sProof.proofSubSet(dp1.sub(0), dp2.sub(0));
            }
        } else if (dp2.op().equals(depLDT.getNoW())) {
            if (dp1.op().equals(depLDT.getNoRaW()) || dp1.op().equals(depLDT.getNoWaR())
                    || dp1.op().equals(depLDT.getNoWaW())) {
                return sProof.proofSubSet(dp1.sub(0), dp2.sub(0));
            }
        }
        return false;
    }

    private Set<Term> weakeningDependencePredicates(Term unProven) {
        Set<Term> result = new HashSet<>();

        // System.out.println("Weaken by Pred symbol for " + unProven + ": ");
        if (unProven != null) {
            result.addAll(weakenByPredicateSymbol(unProven));

            // System.out.println("Weaken by Index for "+unProven);
            result.addAll(weakenByDividingOverIndex(unProven));
            if (itrNumber < 1) {

                // System.out.println("Weaken by Subset for "+unProven);
                result.addAll(weakenBySubSet(unProven));
            }
        }
        return result;
    }

    private Set<Term> weakenByPredicateSymbol(Term unProven) {
        Set<Term> result = new HashSet<>();
        if (unProven.op().equals(depLDT.getNoR())) {
            result.add(tb.noRaW(unProven.sub(0)));
            result.add(tb.noWaR(unProven.sub(0)));
            // result.add(tb.relaxedNoRaW(unProven.sub(0), tb.empty(), tb.empty(), tb.empty()));
            // result.add(tb.relaxedNoWaR(unProven.sub(0), tb.empty(), tb.empty(), tb.empty()));
        } else if (unProven.op().equals(depLDT.getNoW())) {
            result.add(tb.noRaW(unProven.sub(0)));
            result.add(tb.noWaR(unProven.sub(0)));
            result.add(tb.noWaW(unProven.sub(0)));
            // result.add(tb.relaxedNoRaW(unProven.sub(0), tb.empty(), tb.empty(), tb.empty()));
            // result.add(tb.relaxedNoWaR(unProven.sub(0), tb.empty(), tb.empty(), tb.empty()));
            // result.add(tb.relaxedNoWaW(unProven.sub(0), tb.empty(), tb.empty()));
        } else if (unProven.op().equals(depLDT.getRelaxedNoR())) {
            result.add(tb.relaxedNoRaW(unProven.sub(0), tb.empty(), tb.empty(), tb.empty()));
            result.add(tb.relaxedNoWaR(unProven.sub(0), tb.empty(), tb.empty(), tb.empty()));
        } else if (unProven.op().equals(depLDT.getRelaxedNoW())) {
            result.add(tb.relaxedNoRaW(unProven.sub(0), tb.empty(), tb.empty(), tb.empty()));
            result.add(tb.relaxedNoWaR(unProven.sub(0), tb.empty(), tb.empty(), tb.empty()));
            result.add(tb.relaxedNoWaW(unProven.sub(0), tb.empty(), tb.empty()));
        }

        return result;
    }

    private Set<Term> weakenByDividingOverIndex(Term pred) {
        Set<Term> result = new HashSet<>();
        if (pred.sub(0).op() == locsetLDT.getArrayRange())
            result = weakenByDividingOverIndexForArrayRange(pred);
        else if (pred.sub(0).op() == locsetLDT.getMatrixRange())
            result = weakenByDividingOverIndexForMatrixRange(pred);
        return result;
    }

    private Set<Term> weakenBySubSet(Term pred) {
        Set<Term> result = new HashSet<>();
        if (pred.sub(0).op() == locsetLDT.getArrayRange())
            result = weakenBySubSetForArrayRange(pred);
        else if (pred.sub(0).op() == locsetLDT.getMatrixRange())
            result = weakenBySubSetForMatrixRange(pred);
        return result;
    }

    private Set<Term> weakenBySubSetForArrayRange(Term unProven) {
        Set<Term> result = new HashSet<>();
        final Term locSet = unProven.sub(0);

        final Term array = locSet.sub(0);
        final Term low = locSet.sub(1);
        final Term high = locSet.sub(2);
        final Term newLow = tb.add(low, tb.one());
        final Term newHigh = tb.sub(high, tb.one());

        if (!sProof.proofEquality(low, high)) {
            final Term lowSingleton = tb.singleton(array, tb.arr(low));
            final Term highSingleton = tb.singleton(array, tb.arr(high));

            Term subLoc;
            if (sProof.proofLT(tb.zero(), newHigh)) {
                if (sProof.proofLT(newLow, newHigh)) {
                    subLoc = tb.arrayRange(array, newLow, newHigh);
                } else if (sProof.proofEquality(newLow, newHigh)) {
                    subLoc = tb.singleton(array, tb.arr(newLow));
                } else {
                    // should not happen, weaken to essentially tru
                    subLoc = tb.empty();
                }

                if (depLDT.isDependencePredicate(unProven.op())) {
                    final JFunction op = (JFunction) unProven.op();
                    result.add(tb.func(op, subLoc));
                    result.add(tb.func(op, lowSingleton));
                    result.add(tb.func(op, highSingleton));
                }
            }
        }
        return result;
    }

    private Set<Term> weakenBySubSetForMatrixRange(Term unProven) {
        Set<Term> result = new HashSet<>();
        final Term locSet = unProven.sub(0);

        final Term heap = locSet.sub(0);
        final Term arr = locSet.sub(1);
        final Term outLow = locSet.sub(2);
        final Term outHigh = locSet.sub(3);
        final Term inLow = locSet.sub(4);
        final Term inHigh = locSet.sub(5);


        final Term newOutLow = tb.add(outLow, tb.one());
        final Term newOutHigh = tb.sub(outHigh, tb.one());

        final Term newInLow = tb.add(inLow, tb.one());
        final Term newInHigh = tb.sub(inHigh, tb.one());

        if (!sProof.proofEquality(outLow, outHigh)) {
            final Term lowArr = tb.matrixRange(heap, arr, outLow, outLow, inLow, inHigh);
            final Term highArr = tb.matrixRange(heap, arr, outHigh, outHigh, inLow, inHigh);

            Term subLoc;
            if (sProof.proofLT(tb.zero(), newOutHigh)) {
                if (sProof.proofLEQ(newOutLow, newOutHigh)) {
                    subLoc = tb.matrixRange(heap, arr, newOutLow, newOutHigh, inLow, inHigh);
                } else {
                    // should not happen, weaken to essentially true
                    subLoc = tb.empty();
                }

                if (depLDT.isDependencePredicate(unProven.op())) {
                    final JFunction op = (JFunction) unProven.op();
                    result.add(tb.func(op, subLoc));
                    result.add(tb.func(op, lowArr));
                    result.add(tb.func(op, highArr));
                }
            }
        }

        if (!sProof.proofEquality(inLow, inHigh)) {
            final Term lowArr = tb.matrixRange(heap, arr, outLow, outHigh, inLow, inLow);
            final Term highArr = tb.matrixRange(heap, arr, outLow, outHigh, inHigh, inHigh);

            Term subLoc;
            if (sProof.proofLT(tb.zero(), newInHigh)) {
                if (sProof.proofLEQ(newInLow, newInHigh)) {
                    subLoc = tb.matrixRange(heap, arr, outLow, outHigh, newInLow, newInHigh);
                } else {
                    // should not happen, weaken to essentially true
                    subLoc = tb.empty();
                }

                if (depLDT.isDependencePredicate(unProven.op())) {
                    final JFunction op = (JFunction) unProven.op();
                    result.add(tb.func(op, subLoc));
                    result.add(tb.func(op, lowArr));
                    result.add(tb.func(op, highArr));
                }
            }
        }


        return result;
    }

    private Set<Term> weakenByDividingOverIndexForArrayRange(Term pred) {
        Set<Term> result = new HashSet<>();
        Term locSet = pred.sub(0);

        if (locSet != null) {
            // System.out.println("Find Loc Set: "+locSet);
            Term array = locSet.sub(0);

            Term low = locSet.sub(1);
            Term high = locSet.sub(2);

            Term lowToInner, innerToHigh;
            Term lowToOuter, outerToHigh;
            // System.out.println("low: "+ low + ", index: "+ indexInner + ", high: " + high);
            if (array == arrInner) {
                if (!sProof.proofEquality(low, indexInner)) {
                    if (!sProof.proofEquality(indexInner, high)) {
                        lowToInner = tb.arrayRange(array, low, indexInner);
                        innerToHigh = tb.arrayRange(array, indexInner, high);
                        // if(sProof.proofLT(low, tb.subtract(index, tb.one())) &&
                        // sProof.proofLT(tb.add(index, tb.one()), high)) {
                        // lowToI = tb.arrayRange(array, low, tb.subtract(index, tb.one()));
                        // iToHigh = tb.arrayRange(array, tb.add(index, tb.one()), high);
                        // }
                    } else {
                        lowToInner = tb.arrayRange(array, low, indexInner);
                        innerToHigh = tb.singleton(array, tb.arr(indexInner));
                    }
                } else {
                    if (!sProof.proofEquality(indexInner, high)) {
                        innerToHigh = tb.arrayRange(array, indexInner, high);
                        lowToInner = tb.singleton(array, tb.arr(indexInner));
                    } else {
                        lowToInner = tb.singleton(array, tb.arr(indexInner));
                        innerToHigh = tb.singleton(array, tb.arr(indexInner));
                    }
                }
                if (lowToInner != null && innerToHigh != null) {
                    if (depLDT.isDependencePredicate(pred.op())) {
                        final JFunction dependencyOp = (JFunction) pred.op();
                        result.add(tb.func(dependencyOp, lowToInner));
                        result.add(tb.func(dependencyOp, innerToHigh));
                    }
                }
            }

            if (!sProof.proofEquality(low, indexOuter)) {
                if (!sProof.proofEquality(indexOuter, high)) {
                    lowToOuter = tb.arrayRange(array, low, indexOuter);
                    outerToHigh = tb.arrayRange(array, indexOuter, high);
                    // if(sProof.proofLT(low, tb.subtract(index, tb.one())) &&
                    // sProof.proofLT(tb.add(index, tb.one()), high)) {
                    // lowToI = tb.arrayRange(array, low, tb.subtract(index, tb.one()));
                    // iToHigh = tb.arrayRange(array, tb.add(index, tb.one()), high);
                    // }
                } else {
                    lowToOuter = tb.arrayRange(array, low, indexOuter);
                    outerToHigh = tb.singleton(array, tb.arr(indexOuter));
                }
            } else {
                if (!sProof.proofEquality(indexOuter, high)) {
                    outerToHigh = tb.arrayRange(array, indexOuter, high);
                    lowToOuter = tb.singleton(array, tb.arr(indexOuter));
                } else {
                    lowToOuter = tb.singleton(array, tb.arr(indexOuter));
                    outerToHigh = tb.singleton(array, tb.arr(indexOuter));
                }
            }
            if (lowToOuter != null && outerToHigh != null) {
                if (depLDT.isDependencePredicate(pred.op())) {
                    final JFunction dependencyOp = (JFunction) pred.op();
                    result.add(tb.func(dependencyOp, lowToOuter));
                    result.add(tb.func(dependencyOp, outerToHigh));
                }
            }
        }

        // System.out.println(result);
        return result;
    }

    private Set<Term> weakenByDividingOverIndexForMatrixRange(Term pred) {
        Set<Term> result = new HashSet<>();
        Term locSet = pred.sub(0);

        if (locSet != null) {
            final Term heap = locSet.sub(0);
            final Term arr = locSet.sub(1);
            final Term outLow = locSet.sub(2);
            final Term outHigh = locSet.sub(3);
            final Term inLow = locSet.sub(4);
            final Term inHigh = locSet.sub(5);

            Term lowToInner, innerToHigh;
            Term lowToOuter, outerToHigh;
            if (arr == arrInner) {
                if (sProof.proofLEQ(inLow, indexInner)) {
                    lowToInner = tb.matrixRange(heap, arr, outLow, outHigh, inLow, indexInner);
                    if (sProof.proofLEQ(indexInner, inHigh)) {
                        innerToHigh =
                            tb.matrixRange(heap, arr, outLow, outHigh, indexInner, inHigh);
                    } else {
                        innerToHigh = tb.empty();
                    }
                } else {
                    lowToInner = tb.empty();
                    if (sProof.proofLEQ(indexInner, inHigh)) {
                        innerToHigh =
                            tb.matrixRange(heap, arr, outLow, outHigh, indexInner, inHigh);
                    } else {
                        innerToHigh = tb.empty();
                    }
                }

                if (depLDT.isDependencePredicate(pred.op())) {
                    final JFunction dependencyOp = (JFunction) pred.op();
                    if (lowToInner != null && lowToInner != tb.empty()) {
                        result.add(tb.func(dependencyOp, lowToInner));
                    }
                    if (innerToHigh != null && innerToHigh != tb.empty()) {
                        result.add(tb.func(dependencyOp, innerToHigh));
                    }
                }
            }
            if (arr == arrOuter) {
                if (sProof.proofLEQ(outLow, indexOuter)) {
                    lowToOuter = tb.matrixRange(heap, arr, outLow, indexOuter, inLow, inHigh);
                    if (sProof.proofLEQ(indexOuter, outHigh)) {
                        outerToHigh = tb.matrixRange(heap, arr, indexOuter, outHigh, inLow, inHigh);
                    } else {
                        outerToHigh = tb.empty();
                    }
                } else {
                    lowToOuter = tb.empty(); // tb.arrayRange(arr, inLow, inHigh);//
                    if (sProof.proofLEQ(indexOuter, outHigh)) {
                        outerToHigh = tb.matrixRange(heap, arr, indexOuter, outHigh, inLow, inHigh);
                    } else {
                        outerToHigh = tb.empty();// matrixRange(heap, arr, indexOuter, indexOuter,
                                                 // inLow, inHigh)
                    }
                }
                if (depLDT.isDependencePredicate(pred.op())) {
                    final JFunction dependencyOp = (JFunction) pred.op();
                    if (lowToOuter != null && lowToOuter != tb.empty()) {
                        result.add(tb.func(dependencyOp, lowToOuter));
                    }
                    if (outerToHigh != null && outerToHigh != tb.empty()) {
                        result.add(tb.func(dependencyOp, outerToHigh));
                    }

                }
            }
        }
        // System.out.println("weakening res for: "+ pred + " is:"+ result);
        return result;
    }


    private Set<Term> weakeningComparisonPredicates(Term pred) {
        Set<Term> result = new HashSet<>();
        if (pred != null) {
            result = compPredWeakeningByPredicates(pred);
            // result.addAll(compPredWeakenByIndex(pred));
            // System.out.println("Weakening by Predicate for: " + pred);
            // System.out.println("Weakening by Heuristics for: " + pred);
            if (itrNumber < 1) {
                result.addAll(compPredWeakeningByHeuristics(pred));
            }
        }
        return result;
    }

    // private Set<Term> compPredWeakenByIndex(Term pred) {
    // Set<Term> result = new HashSet<>();
    // Term left = pred.sub(0);
    // Term right = pred.sub(1);
    // if (left != null && right != null && index != null) {
    // if (pred.op() == intLDT.getLessThan()) {
    // result.add(tb.lt(left, index));
    // result.add(tb.lt(index, right));
    // } else if (pred.op() == intLDT.getGreaterThan()) {
    // result.add(tb.gt(left, index));
    // result.add(tb.gt(index, right));
    // } else if (pred.op() == Equality.EQUALS) {
    // result.add(tb.equals(left, index));
    // result.add(tb.equals(index, right));
    // } else if (pred.op() == intLDT.getLessOrEquals()) {
    // result.add(tb.leq(left, index));
    // result.add(tb.leq(index, right));
    // } else if (pred.op() == intLDT.getGreaterOrEquals()) {
    // result.add(tb.geq(left, index));
    // result.add(tb.geq(index, right));
    // }
    // }
    // return result;
    // }

    private Set<Term> compPredWeakeningByPredicates(Term pred) {
        Set<Term> result = new HashSet<>();
        if (pred.arity() == 2) { // added because of not(equal(a,null))
            Term low = pred.sub(0);
            Term high = pred.sub(1);
            if (low != null && high != null) {
                if (pred.op() == intLDT.getLessThan()) {
                    result.add(tb.leq(low, high));
                } else if (pred.op() == intLDT.getGreaterThan()) {
                    result.add(tb.geq(low, high));
                } else if (pred.op() == intLDT.getLessOrEquals()) {// Think again
                    result.add(tb.gt(low, high));
                    result.add(tb.equals(low, high));
                } else if (pred.op() == intLDT.getGreaterOrEquals()) {// Think again
                    result.add(tb.lt(low, high));
                    result.add(tb.equals(low, high));
                } else if (pred.op() == Equality.EQUALS) {
                    result.add(tb.gt(low, high));
                    result.add(tb.lt(low, high));
                }
            }
            // System.out.println(result);
        }
        return result;
    }

    private Set<Term> compPredWeakeningByHeuristics(Term pred) {
        Set<Term> result = new HashSet<>();
        if (pred.arity() == 2) {
            Term left = pred.sub(0);
            Term right = pred.sub(1);
            if (left != null && right != null) {
                if (pred.op() == intLDT.getLessThan()) {
                    result.add(tb.lt(left, tb.add(right, tb.one())));
                } else if (pred.op() == intLDT.getGreaterThan()) {
                    result.add(tb.gt(left, tb.sub(right, tb.one())));
                } else if (pred.op() == intLDT.getLessOrEquals()) {
                    result.add(tb.leq(left, tb.add(right, tb.one())));
                } else if (pred.op() == intLDT.getGreaterOrEquals()) {
                    result.add(tb.geq(left, tb.sub(right, tb.one())));
                } else if (pred.op() == Equality.EQUALS) {
                    result.add(tb.geq(left, right));
                    result.add(tb.leq(right, left));
                }
            }
        }
        // System.out.println(result);
        return result;
    }
}
