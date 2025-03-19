package de.uka.ilkd.key.loopinvgen;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.equality.RenamingTermProperty;
import de.uka.ilkd.key.logic.op.Equality;
import de.uka.ilkd.key.logic.op.JFunction;
import de.uka.ilkd.key.proof.io.ProofSaver;
import org.key_project.util.collection.Pair;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Set;

/**
 * Refinement of the predicates describing the loop index and the dependency predicates
 */
public class LoopIndexAndDependencyPredicateRefiner extends PredicateRefiner {

    private final Term innerIndex;
    private final Term outerIndex;
    private final int itrNumber;
    private Set<Term> depPredicates;
    private Set<Term> compPredicates;

    private Graph<Term> locSetToPredicate;

    public LoopIndexAndDependencyPredicateRefiner(Sequent sequent, Set<Term> depPredList, Set<Term> compPredList, Term outerIndex,
                                                  Term index, int iteration, Services services) {
        super(sequent, services);
        this.depPredicates = depPredList;
        this.compPredicates = compPredList;
        this.innerIndex = index;
        this.itrNumber = iteration;
        this.outerIndex = outerIndex;
        this.locSetToPredicate = new Graph<>();
    }

    @Override
    public Pair<Set<Term>, Set<Term>> refine() {

        int inlattice = 0;
        Set<Term> unProvenDepPreds = new HashSet<>();
        for (Term pred : depPredicates) {
            if (depLDT.isDependencePredicate(pred.op())) {
//				System.out.println("abel + 1 " + pred);
                if (locSetToPredicate.hasVertex(pred.sub(0)) && locSetToPredicate.hasEdge(pred.sub(0), pred)) {
//					System.out.println("In lattice " + pred);
                    inlattice++;
                } else if (sequentImpliesPredicate(pred)) {
                    locSetToPredicate.addEdge(pred.sub(0), pred, false);
                    if (pred.op() == depLDT.getNoR()) {
                        locSetToPredicate.addEdge(pred.sub(0), tb.noRaW(pred.sub(0)), false);
                        locSetToPredicate.addEdge(pred.sub(0), tb.noWaR(pred.sub(0)), false);
                    } else if (pred.op() == depLDT.getNoW()) {
                        locSetToPredicate.addEdge(pred.sub(0), tb.noRaW(pred.sub(0)), false);
                        locSetToPredicate.addEdge(pred.sub(0), tb.noWaR(pred.sub(0)), false);
                        locSetToPredicate.addEdge(pred.sub(0), tb.noWaW(pred.sub(0)), false);
                    } else if (pred.op() == depLDT.getRelaxedNoR()) {
                        locSetToPredicate.addEdge(pred.sub(0), tb.relaxedNoRaW(pred.sub(0), tb.empty(), tb.empty(), tb.empty()), false);
                        locSetToPredicate.addEdge(pred.sub(0), tb.relaxedNoWaR(pred.sub(0), tb.empty(), tb.empty(), tb.empty()), false);
                    } else if (pred.op() == depLDT.getRelaxedNoW()) {
                        locSetToPredicate.addEdge(pred.sub(0), tb.relaxedNoRaW(pred.sub(0), tb.empty(), tb.empty(), tb.empty()), false);
                        locSetToPredicate.addEdge(pred.sub(0), tb.relaxedNoWaR(pred.sub(0), tb.empty(), tb.empty(), tb.empty()), false);
                        locSetToPredicate.addEdge(pred.sub(0), tb.relaxedNoWaW(pred.sub(0), tb.empty(), tb.empty()), false);
                    }
                } else {
                    unProvenDepPreds.add(pred);
//				System.out.println("Here: 2");
                }
            }

        }
        depPredicates.removeAll(unProvenDepPreds);
        Set<Term> weakenedDepPreds = new HashSet<>();
        for (Term un : unProvenDepPreds) {
            weakenedDepPreds.addAll(weakeningDependencePredicates(un));
        }


        for (Term w : weakenedDepPreds) {
            if (w.arity() > 0) {
//				System.out.println("Checking lattice for: " + w);
                if (locSetToPredicate.hasVertex(w.sub(0)) && locSetToPredicate.hasEdge(w.sub(0), w)) {
                    depPredicates.add(w);
//					System.out.println("In lattice: " + w);
                    inlattice++;
                } else {
                    if (sequentImpliesPredicate(w)) {
                        depPredicates.add(w);
                        locSetToPredicate.addEdge(w.sub(0), w, false);
                        if (w.op() == depLDT.getNoR()) {
                            locSetToPredicate.addEdge(w.sub(0), tb.noRaW(w.sub(0)), false);
                            locSetToPredicate.addEdge(w.sub(0), tb.noWaR(w.sub(0)), false);
                        } else if (w.op() == depLDT.getNoW()) {
                            locSetToPredicate.addEdge(w.sub(0), tb.noRaW(w.sub(0)), false);
                            locSetToPredicate.addEdge(w.sub(0), tb.noWaR(w.sub(0)), false);
                            locSetToPredicate.addEdge(w.sub(0), tb.noWaW(w.sub(0)), false);
                        } else if (w.op() == depLDT.getRelaxedNoR()) {
                            locSetToPredicate.addEdge(w.sub(0), tb.relaxedNoRaW(w.sub(0), tb.empty(), tb.empty(), tb.empty()), false);
                            locSetToPredicate.addEdge(w.sub(0), tb.relaxedNoWaR(w.sub(0), tb.empty(), tb.empty(), tb.empty()), false);
                        } else if (w.op() == depLDT.getRelaxedNoW()) {
                            locSetToPredicate.addEdge(w.sub(0), tb.relaxedNoRaW(w.sub(0), tb.empty(), tb.empty(), tb.empty()), false);
                            locSetToPredicate.addEdge(w.sub(0), tb.relaxedNoWaR(w.sub(0), tb.empty(), tb.empty(), tb.empty()), false);
                            locSetToPredicate.addEdge(w.sub(0), tb.relaxedNoWaW(w.sub(0), tb.empty(), tb.empty()), false);
                        }
                    }
                }
            }
        }
//		System.out.println("Lattice was useful " + inlattice + " times");
//		System.out.println("DEP PREDS: " + depPredicates);
        // -------------------------------------
        Set<Term> unProvenCompPreds = new HashSet<>();
        for (Term pred : compPredicates) {
//			System.out.println("Proving Comp Pred: " + pred);
            if (!sequentImpliesPredicate(pred)) {
//				System.out.println("not proved Inner: "+pred);
                unProvenCompPreds.add(pred);
            }
        }
        compPredicates.removeAll(unProvenCompPreds);
        Set<Term> weakenedCompPreds = new HashSet<>();
        for (Term un : unProvenCompPreds) {
            weakenedCompPreds.addAll(weakeningComparisonPredicates(un));
        }

        for (Term w : weakenedCompPreds) {
//			System.out.println("Proving Weakened Comp Pred: " + w);
            if (sequentImpliesPredicate(w)) {
                compPredicates.add(w);
            }
        }
//		System.out.println("COMP PREDS: " + compPredicates);
        return new Pair<>(depPredicates, compPredicates);
    }

    // tries to prove that dp2 -> dp1, i.e. noX(l2) -> noY(l1)
    private boolean predicateImpliedBypredicate(Term dp1, Term dp2) {
        if (dp1.op() == dp2.op() && sProof.proofSubSet(dp1.sub(0), dp2.sub(0))) {
            return true;
        } else if (dp2.op().equals(depLDT.getNoR())) {
            if (dp1.op().equals(depLDT.getNoRaW()) || dp1.op().equals(depLDT.getNoWaR()) ||
                    dp1.op().equals(depLDT.getRelaxedNoRaW()) || dp1.op().equals(depLDT.getRelaxedNoWaR())) {

                if (dp1.sub(0).equalsModProperty(dp2.sub(0), RenamingTermProperty.RENAMING_TERM_PROPERTY)) {
                    return true;
                }

                return sProof.proofSubSet(dp1.sub(0), dp2.sub(0));
            }
        } else if (dp2.op().equals(depLDT.getNoW())) {
            if (dp1.op().equals(depLDT.getNoRaW()) || dp1.op().equals(depLDT.getNoWaR())
                    || dp1.op().equals(depLDT.getNoWaW()) ||
                    dp1.op().equals(depLDT.getRelaxedNoRaW()) || dp1.op().equals(depLDT.getRelaxedNoWaR())
                    || dp1.op().equals(depLDT.getRelaxedNoWaW())) {

                if (dp1.sub(0).equalsModProperty(dp2.sub(0), RenamingTermProperty.RENAMING_TERM_PROPERTY)) {
                    return true;
                }


                return sProof.proofSubSet(dp1.sub(0), dp2.sub(0));
            }
        } else if (dp2.op().equals(depLDT.getRelaxedNoR())) {
            if (dp1.op().equals(depLDT.getRelaxedNoRaW()) || dp1.op().equals(depLDT.getRelaxedNoWaR())) {
                if (dp1.sub(0).equalsModProperty(dp2.sub(0), RenamingTermProperty.RENAMING_TERM_PROPERTY)) {
                    return true;
                }

                return sProof.proofSubSet(dp1.sub(0), dp2.sub(0));
            }
        } else if (dp2.op().equals(depLDT.getRelaxedNoW())) {
            if (dp1.op().equals(depLDT.getRelaxedNoRaW()) || dp1.op().equals(depLDT.getRelaxedNoWaR())
                    || dp1.op().equals(depLDT.getRelaxedNoWaW())) {

                if (dp1.sub(0).equalsModProperty(dp2.sub(0), RenamingTermProperty.RENAMING_TERM_PROPERTY)) {
                    return true;
                }

                return sProof.proofSubSet(dp1.sub(0), dp2.sub(0));
            }
        }
        return false;
    }

    private Set<Term> weakeningDependencePredicates(Term unProven) {
        Set<Term> result = new HashSet<>();

//		**
        if (unProven != null) {
//		System.out.println("Weaken " + unProven + ": ");
            result.addAll(weakenByPredicateSymbol(unProven));

//		System.out.println("Weaken by Index for "+unProven);
            result.addAll(weakenByDividingOverIndex(unProven));
//			System.out.println("Weakening for iteration: " + itrNumber);
            if (itrNumber < 1) {
//			System.out.println("Weaken by Subset for "+unProven);
                result.addAll(weakenBySubSet(unProven));
            }
        }
        if (result.isEmpty()) {
//			System.out.println("Weakening didn't succeed");
            result.add(tb.tt());
        }
//		System.out.println("WEAKENING RESULT: "+result);
        return result;
    }

    private Set<Term> weakenByPredicateSymbol(Term unProven) {
        Set<Term> result = new HashSet<>();
        if (unProven.op().equals(depLDT.getNoR())) {
            result.add(tb.noRaW(unProven.sub(0)));
            result.add(tb.noWaR(unProven.sub(0)));
            //		result.add(tb.relaxedNoRaW(unProven.sub(0), tb.empty(), tb.empty(), tb.empty()));
            //		result.add(tb.relaxedNoWaR(unProven.sub(0), tb.empty(), tb.empty(), tb.empty()));
        } else if (unProven.op().equals(depLDT.getNoW())) {
            result.add(tb.noRaW(unProven.sub(0)));
            result.add(tb.noWaR(unProven.sub(0)));
            result.add(tb.noWaW(unProven.sub(0)));
//			result.add(tb.relaxedNoRaW(unProven.sub(0), tb.empty(), tb.empty(), tb.empty()));
//			result.add(tb.relaxedNoWaR(unProven.sub(0), tb.empty(), tb.empty(), tb.empty()));
//			result.add(tb.relaxedNoWaW(unProven.sub(0), tb.empty(), tb.empty()));
        } else if (unProven.op().equals(depLDT.getRelaxedNoR())) {
            result.add(tb.relaxedNoRaW(unProven.sub(0), tb.empty(), tb.empty(), tb.empty()));
            result.add(tb.relaxedNoWaR(unProven.sub(0), tb.empty(), tb.empty(), tb.empty()));
        } else if (unProven.op().equals(depLDT.getRelaxedNoW())) {
            result.add(tb.relaxedNoRaW(unProven.sub(0), tb.empty(), tb.empty(), tb.empty()));
            result.add(tb.relaxedNoWaR(unProven.sub(0), tb.empty(), tb.empty(), tb.empty()));
            result.add(tb.relaxedNoWaW(unProven.sub(0), tb.empty(), tb.empty()));
        }

//		System.out.println("weaken by pred symb "+ unProven +" with "+ result);
        for (Term r : result) {
            if (locSetToPredicate.hasVertex(r.sub(0))) {
                locSetToPredicate.addEdge(r.sub(0), r, false);
//				System.out.println("added 1");
            }
        }
//		System.out.println("weaken by predicate symb for " + unProven + " is "+result);
//		System.out.println("size: " + result.size());
        return result;
    }

    private Set<Term> weakenBySubSet(Term pred) {
        if (pred.sub(0).op() == locsetLDT.getArrayRange())
            return weakenBySubSetForArrayRange(pred);
        else if (pred.sub(0).op() == locsetLDT.getMatrixRange())
            return weakenBySubSetForMatrixRange(pred);
        else {
            System.out.println("Error: " + ProofSaver.printAnything(pred, services));
            Set<Term> result = new HashSet<>();
            result.add(services.getTermBuilder().tt());
            return result;
        }
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
                    if (op == depLDT.getRelaxedNoRaW() || op == depLDT.getRelaxedNoWaR()) {
                        result.add(tb.func(op, subLoc, tb.empty(), tb.empty(), tb.empty()));
                        result.add(tb.func(op, lowSingleton, tb.empty(), tb.empty(), tb.empty()));
                        result.add(tb.func(op, highSingleton, tb.empty(), tb.empty(), tb.empty()));
                    } else if (op == depLDT.getRelaxedNoWaW()) {
                        result.add(tb.func(op, subLoc, tb.empty(), tb.empty()));
                        result.add(tb.func(op, lowSingleton, tb.empty(), tb.empty()));
                        result.add(tb.func(op, highSingleton, tb.empty(), tb.empty()));
                    } else {
                        result.add(tb.func(op, subLoc));
                        result.add(tb.func(op, lowSingleton));
                        result.add(tb.func(op, highSingleton));
                    }
                }
            }
        }

//		System.out.println("weaken by subset "+ unProven +" with "+ result);
        return result;

    }

    private Set<Term> weakenBySubSetForMatrixRange(Term unProven) {
        Set<Term> resultArr = new HashSet<>();

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

                    resultArr.add(buildPredicate(unProven, lowArr, op));
                    resultArr.add(buildPredicate(unProven, highArr, op));
                    resultArr.add(buildPredicate(unProven, subLoc, op));

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

                    resultArr.add(buildPredicate(unProven, lowArr, op));
                    resultArr.add(buildPredicate(unProven, highArr, op));
                    resultArr.add(buildPredicate(unProven, subLoc, op));

                }
            }
        }
//		System.out.println("weaken by subset for " + unProven + " is " +result);
//		System.out.println("size: " + result.size());

        return resultArr;
    }


    private Set<Term> weakenByDividingOverIndex(Term pred) {
        if (pred.sub(0).op() == locsetLDT.getArrayRange())
            return weakenByDividingOverIndexForArrayRange(pred);
        else if (pred.sub(0).op() == locsetLDT.getMatrixRange())
            return weakenByDividingOverIndexForMatrixRange(pred);
        else return new HashSet<>();
    }

    private Set<Term> weakenByDividingOverIndexForArrayRange(Term pred) {

        Set<Term> resultArr = new HashSet<>();
        Term locSet = pred.sub(0);
        if (locSet != null && locSet.arity() == 3) {
//			System.out.println("Find Loc Set: "+locSet);
            Term array = locSet.sub(0);
            Term low = locSet.sub(1);
            Term high = locSet.sub(2);
            Term lowToI = tb.empty();
            Term iToHigh = tb.empty();
            Term lowToIPlusOne = tb.empty();
            Term iPlusOneToHigh = tb.empty();
//			System.out.println("low: "+ low + ", index: "+ index + ", high: " + high);
            if (array != null && low != null && high != null && innerIndex != null) {
                if (!sProof.proofEquality(low, innerIndex)) {
                    if (!sProof.proofEquality(innerIndex, high)) {
                        lowToI = tb.arrayRange(array, low, innerIndex);
                        iToHigh = tb.arrayRange(array, innerIndex, high);
                        if (sProof.proofLT(tb.add(innerIndex, tb.one()), high)) {
                            lowToIPlusOne = tb.arrayRange(array, low, tb.add(innerIndex, tb.one()));
                            iPlusOneToHigh = tb.arrayRange(array, tb.add(innerIndex, tb.one()), high);
                        }
                    } else {
                        lowToI = tb.arrayRange(array, low, innerIndex);
                        iToHigh = tb.singleton(array, tb.arr(innerIndex));
                    }
                } else {
                    if (!sProof.proofEquality(innerIndex, high)) {
                        iToHigh = tb.arrayRange(array, innerIndex, high);
                        lowToI = tb.singleton(array, tb.arr(innerIndex));

                        if (sProof.proofLT(tb.add(innerIndex, tb.one()), high)) {
                            lowToIPlusOne = tb.arrayRange(array, low, tb.add(innerIndex, tb.one()));
                            iPlusOneToHigh = tb.arrayRange(array, tb.add(innerIndex, tb.one()), high);
                        }
                    } else {
                        lowToI = tb.singleton(array, tb.arr(innerIndex));
                        iToHigh = tb.singleton(array, tb.arr(innerIndex));
                    }
                }
//				if (lowToI != null && iToHigh != null) {
                if (depLDT.isDependencePredicate(pred.op())) {
                    final JFunction dependencyOp = (JFunction) pred.op();

                    resultArr.add(buildPredicate(pred, lowToI, dependencyOp));
                    resultArr = resultArr;
                    resultArr.add(buildPredicate(pred, iToHigh, dependencyOp));
                    resultArr = resultArr;
                    resultArr.add(buildPredicate(pred, lowToIPlusOne, dependencyOp));
                    resultArr = resultArr;
                    resultArr.add(buildPredicate(pred, iPlusOneToHigh, dependencyOp));
                    resultArr = resultArr;

                }
//				}
            }
//		System.out.println(result);
        }

//		System.out.println("weaken by index & pred symb "+ pred +" with "+ result);
        return resultArr;

    }

    private Set<Term> weakenByDividingOverIndexForMatrixRange(Term pred) {
        Set<Term> resultArr = new HashSet<>();
        Term locSet = pred.sub(0);

        if (locSet != null && innerIndex != null && outerIndex != null) {
            final Term heap = locSet.sub(0);
            final Term arr = locSet.sub(1);
            final Term outLow = locSet.sub(2);
            final Term outHigh = locSet.sub(3);
            final Term inLow = locSet.sub(4);
            final Term inHigh = locSet.sub(5);

            final Term innerIndexMinusOne = tb.sub(innerIndex, tb.one());
            final Term innerIndexPlusOne = tb.add(innerIndex, tb.one());

            ArrayList<Term> innersList = new ArrayList<>();
            innersList.add(inLow);
            innersList.add(innerIndex);
            innersList.add(inHigh);

            if (sProof.proofLEQ(inLow, innerIndexMinusOne)) {
                innersList.add(innerIndexMinusOne);
            }

            if (sProof.proofLEQ(innerIndexPlusOne, inHigh)) {
                innersList.add(innerIndexPlusOne);
            }

            final Term[] inners = innersList.toArray(new Term[innersList.size()]);


            final Term outerIndexMinusOne = tb.sub(outerIndex, tb.one());
            final Term outerIndexPlusOne = tb.add(outerIndex, tb.one());

            ArrayList<Term> outersList = new ArrayList<>();
            outersList.add(outLow);
            outersList.add(outerIndex);
            outersList.add(outHigh);

            if (sProof.proofLEQ(outLow, outerIndexMinusOne)) {
                outersList.add(outerIndexMinusOne);
            }
            if (sProof.proofLEQ(outerIndexPlusOne, outHigh)) {
                outersList.add(outerIndexPlusOne);
            }

            final Term[] outers = outersList.toArray(new Term[outersList.size()]);


            Set<Term> matrixes = new HashSet<>();

            HashMap<Pair<Term, Term>, Boolean> cacheLEQ = new HashMap<>();

            for (int i = 0; i < inners.length; i++) {
                for (int j = 0; j < inners.length; j++) {
                    for (int k = 0; k < outers.length; k++) {
                        for (int l = 0; l < outers.length; l++) {
                            if (i != j && k != l) {
                                boolean outerCond = cacheProofResult(outers, cacheLEQ, k, l);
                                boolean innerCond = cacheProofResult(inners, cacheLEQ, i, j);
                                if (outerCond && innerCond) {
                                    Term right = tb.matrixRange(heap, arr, outers[k], outers[l], inners[i], inners[j]);
                                    if (!locSet.equalsModProperty(right, RenamingTermProperty.RENAMING_TERM_PROPERTY)) {
                                        matrixes.add(right);
                                    }
                                }
                            }
                        }
                    }
                }
            }

//			System.out.println("PRED.OP   " + pred.op());
            if (depLDT.isDependencePredicate(pred.op())) {
                final JFunction dependencyOp = (JFunction) pred.op();
                for (Term mtr : matrixes) {
                    resultArr.add(buildPredicate(pred, mtr, dependencyOp));
                }
            }

        }

//		System.out.println("weakening by dividing over index for: "+ pred + " is:"+ resultArr);
        return resultArr;
    }

    private boolean cacheProofResult(Term[] outers, HashMap<Pair<Term, Term>, Boolean> cacheLT, int k, int l) {
        boolean cond;
        Pair<Term, Term> pair = new Pair<>(outers[k], outers[l]);
        Boolean result = cacheLT.get(pair);
        if (result != null) {
            cond = result;
        } else {
            cond = sProof.proofLT(outers[k], outers[l]);
            cacheLT.put(pair, cond);
        }
        return cond;
    }


    private Set<Term> weakeningComparisonPredicates(Term pred) {
        Set<Term> result = new HashSet<>();
        if (pred != null) {
            result = compPredWeakeningByPredicates(pred);
//		result.addAll(compPredWeakenByIndex(pred));
//		System.out.println("Weakening by Predicate for: " + pred);
//		System.out.println("Weakening by Heuristics for: " + pred);
            if (itrNumber < 1) {
                result.addAll(compPredWeakeningByHeuristics(pred));
            }
        }
        return result;
    }

    private Set<Term> compPredWeakeningByPredicates(Term pred) {
        Set<Term> result = new HashSet<>();
        if (pred != null) {
            Term low = null;
            if (pred.arity() > 0)
                low = pred.sub(0);
            Term high = null;
            if (pred.arity() > 1)
                high = pred.sub(1);
            if (low != null && high != null) {
                if (pred.op() == intLDT.getLessThan()) {
                    result.add(tb.leq(low, high));
                } else if (pred.op() == intLDT.getGreaterThan()) {
                    result.add(tb.geq(low, high));
                }
//				else if (pred.op() == intLDT.getLessOrEquals()) {// Think again
//					result.add(tb.gt(low, high));
//					result.add(tb.equals(low, high));
//				} else if (pred.op() == intLDT.getGreaterOrEquals()) {// Think again
//					result.add(tb.lt(low, high));
//					result.add(tb.equals(low, high));
//				}
                else if (pred.op() == Equality.EQUALS) {
                    result.add(tb.gt(low, high));
                    result.add(tb.lt(low, high));
                }
            }
        }
//		System.out.println(result);
        return result;
    }

    private Set<Term> compPredWeakeningByHeuristics(Term pred) {
        Set<Term> result = new HashSet<>();
        if (pred != null) {
            Term left = pred.sub(0);
            Term right = null;
            if (pred.arity() > 1)
                right = pred.sub(1);
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
//		System.out.println(result);
        return result;
    }

    private Term buildPredicate(Term unProven, Term locSet, JFunction op) {
        final Term builtPred;
        assert locSet != null;
//		if (locSet !=tb.empty()){
        if (unProven.arity() == 1) {
            builtPred = tb.func(op, locSet);
        } else if (unProven.arity() == 4) {
            builtPred = tb.func(op, locSet, tb.empty(), tb.empty(), tb.empty());
        } else if (unProven.arity() == 3) {
            builtPred = tb.func(op, locSet, tb.empty(), tb.empty());
        } else throw new IllegalArgumentException("Unexpected predicate " + unProven);
//		}
        return builtPred;
    }

}