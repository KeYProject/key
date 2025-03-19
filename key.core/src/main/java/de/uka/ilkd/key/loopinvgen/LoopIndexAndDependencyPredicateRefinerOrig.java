package de.uka.ilkd.key.loopinvgen;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Equality;
import de.uka.ilkd.key.logic.op.JFunction;
import org.key_project.util.collection.Pair;

import java.util.HashSet;
import java.util.Set;

/**
 * Refinement of the predicates describing the loop index and the dependency predicates
 */
public class LoopIndexAndDependencyPredicateRefinerOrig extends PredicateRefiner {

	private final Term index;
	private final Term indexOuter;
	private final int itrNumber;
	private Set<Term> refinedCompList;
	private Set<Term> refinedDepList;
	private Set<Term> depPredicates;
	private Set<Term> compPredicates;

	public LoopIndexAndDependencyPredicateRefinerOrig(Sequent sequent, Set<Term> depPredList, Set<Term> compPredList, Term outerIndex,
													  Term index, int iteration, Services services) {
		super(sequent, services);
		this.depPredicates  = depPredList;
		this.compPredicates = compPredList;
		this.index = index;
		this.itrNumber = iteration;
		this.indexOuter = outerIndex;
	}

	@Override
	public Pair<Set<Term>, Set<Term>> refine() {
		Set<Term> unProvenDepPreds = new HashSet<>();
		for (Term pred : depPredicates) {
//			System.out.println("Proving Dep Pred: " + pred);
			if (!sequentImpliesPredicate(pred)) {
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
			for (Term dp : depPredicates) {  // to not loose precision here, the refinement needs to have the property that if dp is removed at some point t1 then there will be a time tn which adds w again (or something that implies it)
				if (predicateImpliedBypredicate(w, dp)) {
//					System.out.println("IMPLIED " + w + " by " + dp);
					weakerPredicateIsSubsumed = true;
					break;
				}
			}
			if (!weakerPredicateIsSubsumed && !depPredicates.contains(w)) {
				if (sequentImpliesPredicate(w)) {
					depPredicates.add(w);
				}
			}
		}
		System.out.println("DEP PREDS: " + depPredicates);
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
			if (sequentImpliesPredicate(w)) {
				compPredicates.add(w);
			}
		}
		return new Pair<>(depPredicates, compPredicates);
	}

	// tries to prove that dp2 -> dp1, i.e. noX(l2) -> noY(l1)
	private boolean predicateImpliedBypredicate(Term dp1, Term dp2) {
		if (dp1.op() == dp2.op() && sProof.proofSubSet(dp1.sub(0), dp2.sub(0))) {
			return true;
		} else if (dp2.op().equals(depLDT.getNoR())) {
			if (dp1.op().equals(depLDT.getNoRaW()) || dp1.op().equals(depLDT.getNoWaR()) ||
				dp1.op().equals(depLDT.getRelaxedNoRaW()) || dp1.op().equals(depLDT.getRelaxedNoWaR())) {

				if (dp1.sub(0).equalsModRenaming(dp2.sub(0))) {
					return true;
				}

				return sProof.proofSubSet(dp1.sub(0), dp2.sub(0));
			}
		} else if (dp2.op().equals(depLDT.getNoW())) {
			if (dp1.op().equals(depLDT.getNoRaW()) || dp1.op().equals(depLDT.getNoWaR())
					|| dp1.op().equals(depLDT.getNoWaW()) ||
				dp1.op().equals(depLDT.getRelaxedNoRaW()) || dp1.op().equals(depLDT.getRelaxedNoWaR())
					|| dp1.op().equals(depLDT.getRelaxedNoWaW())) {

				if (dp1.sub(0).equalsModRenaming(dp2.sub(0))) {
					return true;
				}


				return sProof.proofSubSet(dp1.sub(0), dp2.sub(0));
			}
		}  else if (dp2.op().equals(depLDT.getRelaxedNoR())) {
			if (dp1.op().equals(depLDT.getRelaxedNoRaW()) || dp1.op().equals(depLDT.getRelaxedNoWaR())) {
				if (dp1.sub(0).equalsModRenaming(dp2.sub(0))) {
					return true;
				}

				return sProof.proofSubSet(dp1.sub(0), dp2.sub(0));
			}
		} else if (dp2.op().equals(depLDT.getRelaxedNoW())) {
			if (dp1.op().equals(depLDT.getRelaxedNoRaW()) || dp1.op().equals(depLDT.getRelaxedNoWaR())
					|| dp1.op().equals(depLDT.getRelaxedNoWaW())) {

				if (dp1.sub(0).equalsModRenaming(dp2.sub(0))) {
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
		if (unProven!=null) {
//		System.out.println("Weaken " + unProven + ": ");
			result.addAll(weakenByPredicateSymbol(unProven));

//		System.out.println("Weaken by Index for "+unProven);
			result.addAll(weakenByIndexANDPredicate(unProven));
			if (itrNumber < 1) {
//			System.out.println("Weaken by Subset for "+unProven);
				result.addAll(weakenBySubSet(unProven));
			}
//		System.out.println("index added: ");
//		result.addAll(weakenByIndex(unProven));// 0 or 2
//		System.out.println("subset added: ");
//		if (itrNumber < 2)
//			result.addAll(weakenBySubSet(unProven)); // 0 or 3
//		System.out.println("sequent added: ");
//		result.addAll(weakenBySequent(unProven)); // 0 or 1
//		**		
//		System.out.println(result);
		}
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
		}
		else if (unProven.op().equals(depLDT.getRelaxedNoR())) {
			result.add(tb.relaxedNoRaW(unProven.sub(0), tb.empty(), tb.empty(), tb.empty()));
			result.add(tb.relaxedNoWaR(unProven.sub(0), tb.empty(), tb.empty(), tb.empty()));
		} else if (unProven.op().equals(depLDT.getRelaxedNoW())) {
			result.add(tb.relaxedNoRaW(unProven.sub(0), tb.empty(), tb.empty(), tb.empty()));
			result.add(tb.relaxedNoWaR(unProven.sub(0), tb.empty(), tb.empty(), tb.empty()));
			result.add(tb.relaxedNoWaW(unProven.sub(0), tb.empty(), tb.empty()));
		}

		System.out.println("weaken by pred symb "+ unProven +" with "+ result);
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
					final Function op = (Function) unProven.op();
					if(op==depLDT.getRelaxedNoRaW() || op == depLDT.getRelaxedNoWaR()){
						result.add(tb.func(op, subLoc, tb.empty(), tb.empty(), tb.empty()));
						result.add(tb.func(op, lowSingleton, tb.empty(), tb.empty(), tb.empty()));
						result.add(tb.func(op, highSingleton, tb.empty(), tb.empty(), tb.empty()));
					} else if( op == depLDT.getRelaxedNoWaW()){
						result.add(tb.func(op, subLoc, tb.empty(), tb.empty()));
						result.add(tb.func(op, lowSingleton, tb.empty(), tb.empty()));
						result.add(tb.func(op, highSingleton, tb.empty(), tb.empty()));
					}
					else{
						result.add(tb.func(op, subLoc));
						result.add(tb.func(op, lowSingleton));
						result.add(tb.func(op, highSingleton));
					}
				}
			}
		}

		System.out.println("weaken by subset "+ unProven +" with "+ result);
		return result;

	}
	private Set<Term> weakenBySubSetForMatrixRangeOrig(Term unProven) {
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
			final Term lowArr = tb.matrixRange(heap, arr , outLow, outLow, inLow, inHigh);
			final Term highArr = tb.matrixRange(heap, arr , outHigh, outHigh, inLow, inHigh);

			Term subLoc;
			if (sProof.proofLT(tb.zero(), newOutHigh)) {
				if (sProof.proofLT(newOutLow, newOutHigh)) {
					subLoc = tb.matrixRange(heap, arr, newOutLow, newOutHigh, inLow, inHigh);
				} else if (sProof.proofEquality(newOutLow, newOutHigh)) {
					subLoc = tb.matrixRange(heap, arr, newOutLow, newOutLow, inLow, inHigh);
				} else {
					// should not happen, weaken to essentially true
					subLoc = tb.empty();
				}

				if (depLDT.isDependencePredicate(unProven.op())) {
					final Function op = (Function) unProven.op();
					result.add(tb.func(op, subLoc));
					result.add(tb.func(op, lowArr));
					result.add(tb.func(op, highArr));
				}
			}
		}

		if (!sProof.proofEquality(inLow, inHigh)) {
//			final Term lowArr = tb.matrixRange(heap, arr , outLow, outHigh, inLow, inLow);//=empty
//			final Term highArr = tb.matrixRange(heap, arr , outLow, outHigh, inHigh, inHigh);//=empty

			Term subLoc;
			if (sProof.proofLT(tb.zero(), newInHigh)) {
				if (sProof.proofLT(newInLow, newInHigh)) {
					subLoc = tb.matrixRange(heap, arr, inLow, inHigh, newInLow, newInHigh);
				}
//				else if (sProof.proofEquality(newInLow, newInHigh)) {
//					subLoc = tb.matrixRange(heap, arr, inLow, inHigh, newInLow, newInLow);//=empty
//				}
				else {
					// should not happen, weaken to essentially true
					subLoc = tb.empty();
				}

				if (depLDT.isDependencePredicate(unProven.op())) {
					final Function op = (Function) unProven.op();
					result.add(tb.func(op, subLoc));
//					result.add(tb.func(op, lowArr));
//					result.add(tb.func(op, highArr));
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

		final Term lowArr = tb.matrixRange(heap, arr , outLow, outLow, inLow, inHigh);
		final Term highArr = tb.matrixRange(heap, arr , outHigh, outHigh, inLow, inHigh);

		Term subLoc = tb.matrixRange(heap, arr, newOutLow, newOutHigh, inLow, inHigh);

		if (depLDT.isDependencePredicate(unProven.op())) {
			final Function op = (Function) unProven.op();
			result.add(tb.func(op, subLoc));
			result.add(tb.func(op, lowArr));
			result.add(tb.func(op, highArr));
		}


		subLoc = tb.matrixRange(heap, arr, inLow, inHigh, newInLow, newInHigh);

		if (depLDT.isDependencePredicate(unProven.op())) {
			final Function op = (Function) unProven.op();
			result.add(tb.func(op, subLoc));
//					result.add(tb.func(op, lowArr));
//					result.add(tb.func(op, highArr));
		}

		return result;
	}


	private Set<Term> weakenBySubSet(Term pred) {
		if(pred.sub(0).op()  == locsetLDT.getArrayRange())
			return weakenBySubSetForArrayRange(pred);
		else if (pred.sub(0).op() == locsetLDT.getMatrixRange())
			return weakenBySubSetForMatrixRange(pred);
		else return null;
	}

//	private Set<Term> weakenBySequent(Term unProven) {
//		Operator Pred = unProven.op();
//		Term locSet = unProven.sub(0);
//		Set<Term> result = new HashSet<>();
////		System.out.println("for " + unProven + " weaken by sequent added: ");
//		for (SequentFormula sequentFormula1 : seq.antecedent()) {
//			Term seqLocSet1 = sequentFormula1.formula().sub(0);
//			if (sequentFormula1.formula().op() == depLDT.getRPred()) {
////				if (Pred == depLDT.getNoR() && sProof.proofNonEmptyIntersection(locSet, seqLocSet1)) {
////					result.add(tb.noR(tb.setMinus(locSet, seqLocSet1)));
////				} else
//				if (Pred == depLDT.getNoRaW() && sProof.proofNonEmptyIntersection(locSet, seqLocSet1)) {
//					for (SequentFormula sequentFormula2 : seq.antecedent()) {
//						Term seqLocSet2 = sequentFormula2.formula().sub(0);
//						if (sequentFormula2.formula().op() == depLDT.getWPred()
//								&& sProof.proofNonEmptyIntersection(tb.intersect(locSet, seqLocSet1), seqLocSet2)) {
//							Term seqLabel1 = sequentFormula1.formula().sub(1);
//							Term seqLabel2 = sequentFormula2.formula().sub(1);
//							if (sProof.proofLT(seqLabel2, seqLabel1)) {
//								result.add(tb.noRaW(tb.setMinus(locSet, tb.intersect(seqLocSet1, seqLocSet2))));
////								System.out.println("because "+ seqLabel2 + " is less then " + " there is a " + sequentFormula1 + " after "+ sequentFormula2);
//							}
//						}
//					}
//				} else if (Pred == depLDT.getNoWaR() && sProof.proofNonEmptyIntersection(locSet, seqLocSet1)) {
//					for (SequentFormula sequentFormula2 : seq.antecedent()) {
//						Term seqLocSet2 = sequentFormula2.formula().sub(0);
//						if (sequentFormula2.formula().op() == depLDT.getWPred()
//								&& sProof.proofNonEmptyIntersection(tb.intersect(locSet, seqLocSet1), seqLocSet2)) {
//							Term seqLabel1 = sequentFormula1.formula().sub(1);
//							Term seqLabel2 = sequentFormula2.formula().sub(1);
//							if (sProof.proofLT(seqLabel1, seqLabel2)) {
//								result.add(tb.noWaR(tb.setMinus(locSet, tb.intersect(seqLocSet1, seqLocSet2))));
//							}
//						}
//					}
//				}
//			} else if (sequentFormula1.formula().op() == depLDT.getWPred()) {
//				if (sProof.proofNonEmptyIntersection(locSet, seqLocSet1)) {
//					if (Pred == depLDT.getNoW()) {
//						result.add(tb.noW(tb.setMinus(locSet, seqLocSet1)));
//					} else if (Pred == depLDT.getNoWaW()) {
//						for (SequentFormula sequentFormula2 : seq.antecedent()) {
//							Term seqLocSet2 = sequentFormula2.formula().sub(0);
//							if (sequentFormula2.formula().op() == depLDT.getWPred()
//									&& sProof.proofNonEmptyIntersection(tb.intersect(locSet, seqLocSet1), seqLocSet2)) {
//								Term seqLabel1 = sequentFormula1.formula().sub(1);
//								Term seqLabel2 = sequentFormula2.formula().sub(1);
//								if (!sProof.proofEquality(seqLabel1, seqLabel2)) {
//									result.add(tb.noWaW(tb.setMinus(locSet, tb.intersect(seqLocSet1, seqLocSet2))));
//								}
//							}
//						}
//					}
//				}
//
//			}
//		}
////		System.out.println(result);
//		return result;
//	}

	private Term findArrayRange(Term locSet) {
		if (locSet.op() == locsetLDT.getArrayRange()) {
			return locSet;
		}
//		else if(locSet.op()==locsetLDT.getUnion() || locSet.op()==locsetLDT.getIntersect() || locSet.op()==locsetLDT.getSetMinus()) {
//			findArrayRange(locSet.sub(0))
//		}
		return null;
	}
	private Set<Term> weakenByIndexANDPredicateForArrayRange(Term pred) {
		Set<Term> result = new HashSet<>();
		Term locSet = findArrayRange(pred.sub(0));
		if (locSet != null) {
//			System.out.println("Find Loc Set: "+locSet);
			Term array = locSet.sub(0);
			Term low = locSet.sub(1);
			Term high = locSet.sub(2);
			Term lowToI;
			Term iToHigh;
//			System.out.println("low: "+ low + ", index: "+ index + ", high: " + high);
			if (array != null && low != null && high != null && index != null) {
				if (!sProof.proofEquality(low, index)) {
					if (!sProof.proofEquality(index, high)) {
						lowToI = tb.arrayRange(array, low, index);
						iToHigh = tb.arrayRange(array, index, high);
//					if(sProof.proofLT(low, tb.subtract(index, tb.one())) && sProof.proofLT(tb.add(index, tb.one()), high)) {
//						lowToI = tb.arrayRange(array, low, tb.subtract(index, tb.one()));
//						iToHigh = tb.arrayRange(array, tb.add(index, tb.one()), high);
//					}
					} else {
						lowToI = tb.arrayRange(array, low, index);
						iToHigh = tb.singleton(array, tb.arr(index));
					}
				} else {
					if (!sProof.proofEquality(index, high)) {
						iToHigh = tb.arrayRange(array, index, high);
						lowToI = tb.singleton(array, tb.arr(index));
					} else {
						lowToI = tb.singleton(array, tb.arr(index));
						iToHigh = tb.singleton(array, tb.arr(index));
					}
				}
				if (lowToI != null && iToHigh != null) {
					if (depLDT.isDependencePredicate(pred.op())) {
						final Function dependencyOp = (Function) pred.op();
						if(dependencyOp==depLDT.getRelaxedNoRaW() || dependencyOp == depLDT.getRelaxedNoWaR()){
							result.add(tb.func(dependencyOp, lowToI, tb.empty(), tb.empty(), tb.empty()));
							result.add(tb.func(dependencyOp, iToHigh, tb.empty(), tb.empty(), tb.empty()));
						} else if(dependencyOp == depLDT.getRelaxedNoWaW()){
							result.add(tb.func(dependencyOp, lowToI, tb.empty(), tb.empty()));
							result.add(tb.func(dependencyOp, iToHigh, tb.empty(), tb.empty()));
						}
						else{
							result.add(tb.func(dependencyOp, lowToI));
							result.add(tb.func(dependencyOp, iToHigh));
						}

					}
				}
			}
//		System.out.println(result);
		}
		System.out.println("weaken by index & pred symb "+ pred +" with "+ result);
		return result;

	}
	private Set<Term> weakenByIndexesANDPredicateForMatrixRange(Term pred) {
		Set<Term> result = new HashSet<>();
		Term locSet = pred.sub(0);

		final Term heap = locSet.sub(0);
		final Term arr = locSet.sub(1);
		final Term outLow = locSet.sub(2);
		final Term outHigh = locSet.sub(3);
		final Term inLow = locSet.sub(4);
		final Term inHigh = locSet.sub(5);

		Term lowToInner, innerToHigh;
		Term lowToOuter, outerToHigh;


		if (!inLow.equalsModRenaming(index)) {
			lowToInner = tb.matrixRange(heap, arr, outLow, outHigh, inLow, index);
			if (!index.equalsModRenaming(inHigh)) {
				innerToHigh = tb.matrixRange(heap, arr, outLow, outHigh ,index, inHigh);
			} else {
				innerToHigh = tb.empty();
			}
		} else {
			lowToInner = tb.empty();
			if (!index.equalsModRenaming(inHigh)) {
				innerToHigh = tb.matrixRange(heap, arr, outLow, outHigh,index, inHigh);
			} else {
				innerToHigh = tb.empty();
			}
		}
		if (lowToInner != null && innerToHigh != null) {
			if (depLDT.isDependencePredicate(pred.op())) {
				final Function dependencyOp = (Function) pred.op();
				result.add(tb.func(dependencyOp, lowToInner));
				result.add(tb.func(dependencyOp, innerToHigh));
			}
		}
		if (!outLow.equalsModRenaming(indexOuter)) {
			lowToOuter = tb.matrixRange(heap, arr, outLow, indexOuter, inLow, inHigh);
			if (!indexOuter.equalsModRenaming(outHigh)) {
				outerToHigh = tb.matrixRange(heap, arr, indexOuter, outHigh, inLow, inHigh);
			} else {
				outerToHigh = tb.matrixRange(heap,arr,indexOuter, indexOuter,inLow, inHigh);//matrixRange(heap, arr, indexOuter, indexOuter, inLow, inHigh)
			}
		} else {
			lowToOuter = tb.matrixRange(heap, arr, indexOuter, indexOuter, inLow, inHigh); //tb.arrayRange(arr, inLow, inHigh);//
			if (!indexOuter.equalsModRenaming(outHigh)) {
				outerToHigh = tb.matrixRange(heap, arr, indexOuter, outHigh, inLow, inHigh);
			} else {
				outerToHigh = tb.matrixRange(heap,arr,indexOuter, indexOuter,inLow, inHigh);//matrixRange(heap, arr, indexOuter, indexOuter, inLow, inHigh)
			}
		}
		if (lowToOuter != null && outerToHigh != null) {
			if (depLDT.isDependencePredicate(pred.op())) {
				final Function dependencyOp = (Function) pred.op();
				result.add(tb.func(dependencyOp, lowToOuter));
				result.add(tb.func(dependencyOp, outerToHigh));

				if (!lowToOuter.sub(2).equalsModRenaming(lowToOuter.sub(3))) {
					result.add(tb.func(dependencyOp, tb.matrixRange(heap, arr,
							lowToOuter.sub(2),
							tb.sub(lowToOuter.sub(3), tb.one()),
							lowToOuter.sub(4),
							lowToOuter.sub(5))));
				}


				result.add(tb.func(dependencyOp, outerToHigh));

				if (!outerToHigh.sub(2).equalsModRenaming(outerToHigh.sub(3))) {
					result.add(tb.func(dependencyOp, tb.matrixRange(outerToHigh.sub(0), outerToHigh.sub(1),
							tb.add(outerToHigh.sub(2), tb.one()),
							outerToHigh.sub(3),
							outerToHigh.sub(4),
							outerToHigh.sub(5))));
				}
			}
		}
		System.out.println("weakening res for: "+ pred + " is:"+ result);
		return result;
	}


	private Set<Term> weakenByIndexesANDPredicateForMatrixRangeOrig(Term pred) {
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


//			if(arr == arrInner){
			if (!sProof.proofEquality(inLow, index)) {
				lowToInner = tb.matrixRange(heap, arr, outLow, outHigh,inLow, index);
				if (!sProof.proofEquality(index, inHigh)) {
					innerToHigh = tb.matrixRange(heap, arr, outLow, outHigh ,index, inHigh);
				} else {
					innerToHigh = tb.empty();
				}
			} else {
				lowToInner = tb.empty();
				if (!sProof.proofEquality(index, inHigh)) {
					innerToHigh = tb.matrixRange(heap, arr, outLow, outHigh,index, inHigh);
				} else {
					innerToHigh = tb.empty();
				}
			}
			if (lowToInner != null && innerToHigh != null) {
				if (depLDT.isDependencePredicate(pred.op())) {
					final Function dependencyOp = (Function) pred.op();
					result.add(tb.func(dependencyOp, lowToInner));
					result.add(tb.func(dependencyOp, innerToHigh));
				}
			}
//			}
//			if(arr == arrOuter) {
			if (!sProof.proofEquality(outLow, indexOuter)) {
				lowToOuter = tb.matrixRange(heap, arr, outLow, indexOuter, inLow, inHigh);
				if (!sProof.proofEquality(indexOuter, outHigh)) {
					outerToHigh = tb.matrixRange(heap, arr, indexOuter, outHigh, inLow, inHigh);
				} else {
					outerToHigh = tb.matrixRange(heap,arr,indexOuter, indexOuter,inLow, inHigh);//matrixRange(heap, arr, indexOuter, indexOuter, inLow, inHigh)
				}
			} else {
				lowToOuter = tb.matrixRange(heap, arr, indexOuter, indexOuter, inLow, inHigh); //tb.arrayRange(arr, inLow, inHigh);//
				if (!sProof.proofEquality(indexOuter, outHigh)) {
					outerToHigh = tb.matrixRange(heap, arr, indexOuter, outHigh, inLow, inHigh);
				} else {
					outerToHigh = tb.matrixRange(heap,arr,indexOuter, indexOuter,inLow, inHigh);//matrixRange(heap, arr, indexOuter, indexOuter, inLow, inHigh)
				}
			}
			if (lowToOuter != null && outerToHigh != null) {
				if (depLDT.isDependencePredicate(pred.op())) {
					final Function dependencyOp = (Function) pred.op();
					result.add(tb.func(dependencyOp, lowToOuter));
					result.add(tb.func(dependencyOp, outerToHigh));

//						result.add(tb.func(dependencyOp, tb.matrixRange(heap, arr,
//								tb.add(lowToOuter.sub(2), tb.one()),
//								lowToOuter.sub(3),
//								lowToOuter.sub(4),
//								lowToOuter.sub(5))));

//						result.add(tb.func(dependencyOp, tb.matrixRange(heap, arr,
//								tb.add(lowToOuter.sub(2), tb.one()),
//								lowToOuter.sub(3),
//								tb.add(lowToOuter.sub(4), tb.one()),
//								lowToOuter.sub(5))));

//						result.add(tb.func(dependencyOp, tb.matrixRange(heap, arr,
//								lowToOuter.sub(2),
//								lowToOuter.sub(3),
//								tb.add(lowToOuter.sub(4), tb.one()),
//								lowToOuter.sub(5))));

					result.add(tb.func(dependencyOp, tb.matrixRange(heap, arr,
							lowToOuter.sub(2),
							tb.sub(lowToOuter.sub(3), tb.one()),
							lowToOuter.sub(4),
							lowToOuter.sub(5))));

//						result.add(tb.func(dependencyOp, tb.matrixRange(heap, arr,
//								lowToOuter.sub(2),
//								tb.sub(lowToOuter.sub(3), tb.one()),
//								lowToOuter.sub(4),
//								tb.sub(lowToOuter.sub(5), tb.one()))));
//
//						result.add(tb.func(dependencyOp, tb.matrixRange(heap, lowToOuter.sub(1),
//								lowToOuter.sub(2),
//								lowToOuter.sub(3),
//								lowToOuter.sub(4),
//								tb.sub(lowToOuter.sub(5), tb.one()))));



					result.add(tb.func(dependencyOp, outerToHigh));

					result.add(tb.func(dependencyOp, tb.matrixRange(outerToHigh.sub(0), outerToHigh.sub(1),
							tb.add(outerToHigh.sub(2), tb.one()),
							outerToHigh.sub(3),
							outerToHigh.sub(4),
							outerToHigh.sub(5))));

//						result.add(tb.func(dependencyOp, tb.matrixRange(outerToHigh.sub(0), outerToHigh.sub(1),
//								tb.add(outerToHigh.sub(2), tb.one()),
//								outerToHigh.sub(3),
//								tb.add(outerToHigh.sub(4), tb.one()),
//								outerToHigh.sub(5))));
//
//						result.add(tb.func(dependencyOp, tb.matrixRange(outerToHigh.sub(0), outerToHigh.sub(1),
//								outerToHigh.sub(2),
//								outerToHigh.sub(3),
//								tb.add(outerToHigh.sub(4), tb.one()),
//								outerToHigh.sub(5))));
//
//
//						result.add(tb.func(dependencyOp, tb.matrixRange(outerToHigh.sub(0), outerToHigh.sub(1),
//								outerToHigh.sub(2),
//								tb.sub(outerToHigh.sub(3), tb.one()),
//								outerToHigh.sub(4),
//								outerToHigh.sub(5))));
//
//						result.add(tb.func(dependencyOp, tb.matrixRange(outerToHigh.sub(0), outerToHigh.sub(1),
//								outerToHigh.sub(2),
//								tb.sub(outerToHigh.sub(3), tb.one()),
//								outerToHigh.sub(4),
//								tb.sub(outerToHigh.sub(5), tb.one()))));
//
//						result.add(tb.func(dependencyOp, tb.matrixRange(outerToHigh.sub(0), outerToHigh.sub(1),
//								outerToHigh.sub(2),
//								outerToHigh.sub(3),
//								outerToHigh.sub(4),
//								tb.sub(outerToHigh.sub(5), tb.one()))));

				}
			}
		}
//		}

		System.out.println("weakening res for: "+ pred + " is:"+ result);
		return result;
	}

	private Set<Term> weakenByIndexANDPredicate(Term pred) {
		if(pred.sub(0).op()  == locsetLDT.getArrayRange())
			return weakenByIndexANDPredicateForArrayRange(pred);
		else if (pred.sub(0).op() == locsetLDT.getMatrixRange())
			return weakenByIndexesANDPredicateForMatrixRange(pred);
		else return null;
	}

	private Set<Term> weakeningComparisonPredicates(Term pred) {
		Set<Term> result = new HashSet<>();
		if(pred!=null){
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

//	private Set<Term> compPredWeakenByIndex(Term pred) {
//		Set<Term> result = new HashSet<>();
//		Term left = pred.sub(0);
//		Term right = pred.sub(1);
//		if (left != null && right != null && index != null) {
//			if (pred.op() == intLDT.getLessThan()) {
//				result.add(tb.lt(left, index));
//				result.add(tb.lt(index, right));
//			} else if (pred.op() == intLDT.getGreaterThan()) {
//				result.add(tb.gt(left, index));
//				result.add(tb.gt(index, right));
//			} else if (pred.op() == Equality.EQUALS) {
//				result.add(tb.equals(left, index));
//				result.add(tb.equals(index, right));
//			} else if (pred.op() == intLDT.getLessOrEquals()) {
//				result.add(tb.leq(left, index));
//				result.add(tb.leq(index, right));
//			} else if (pred.op() == intLDT.getGreaterOrEquals()) {
//				result.add(tb.geq(left, index));
//				result.add(tb.geq(index, right));
//			}
//		}
//		return result;
//	}

	private Set<Term> compPredWeakeningByPredicates(Term pred) {
		Set<Term> result = new HashSet<>();
		if(pred!=null){
			Term low = pred.sub(0);
			Term high = null;
			if (pred.arity() > 1)
				high = pred.sub(1);
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
		}
//		System.out.println(result);
		return result;
	}

	private Set<Term> compPredWeakeningByHeuristics(Term pred) {
		Set<Term> result = new HashSet<>();
		if(pred!=null) {
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
}