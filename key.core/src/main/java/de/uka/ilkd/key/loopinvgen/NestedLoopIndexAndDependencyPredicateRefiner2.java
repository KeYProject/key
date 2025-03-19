package de.uka.ilkd.key.loopinvgen;

import de.uka.ilkd.key.java.Services;
import org.key_project.logic.Name;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Equality;
import de.uka.ilkd.key.logic.op.JFunction;
import de.uka.ilkd.key.logic.op.LogicVariable;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import org.key_project.util.collection.Pair;

import java.util.HashSet;
import java.util.Set;

/**
 * Refinement of the predicates describing the loop index and the dependency predicates
 */
public class NestedLoopIndexAndDependencyPredicateRefiner2 extends PredicateRefiner {

	private final Term indexOuter;
	private final Term arrOuter;
	private final Term indexInner;
	private final Term arrInner;
	private final int itrNumber;

	private boolean innerLoop;
	private Term m;
	private Set<Term> depPredicates;
	private Set<Term> compPredicates;

	public NestedLoopIndexAndDependencyPredicateRefiner2(Sequent sequent, Set<Term> depPredList, Set<Term> compPredList, Term arrOuter, Term arrInner,
                                                         Term indexOuter, Term indexInner, int iteration, boolean innerLoop, Term m, Services services) {
		super(sequent, services);
		this.depPredicates  = depPredList;
		this.compPredicates = compPredList;
		this.indexOuter = indexOuter;
		this.arrOuter = arrOuter;
		this.indexInner = indexInner;
		this.arrInner = arrInner;
		this.itrNumber = iteration;
		this.innerLoop = innerLoop;
		this.m = m;
	}

	@Override
	public Pair<Set<Term>, Set<Term>> refine() {
		Set<Term> unProvenDepPreds = new HashSet<>();
		for (Term pred : depPredicates) {
			System.out.println("Proving Dep Pred: " + pred);
			if (!sequentImpliesPredicate(pred)) {
//				System.out.println("not implied by the seq: " + pred);
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
			System.out.println("Weak pred: " + w);
			for (Term dp : depPredicates) {  // to not loose precision here, the refinement needs to have the property that if dp is removed at some point t1 then there will be a time tn which adds w again (or something that implies it)
				if (predicateImpliedByPredicate(w, dp)) {
					System.out.println("IMPLIED " + w + " by " + dp);
//					weakerPredicateIsSubsumed = true;
					break;
				}
			}
			if (!weakerPredicateIsSubsumed && !depPredicates.contains(w)) {
				if (sequentImpliesPredicate(w)) {
					depPredicates.add(w);
				}
			}
		}
//		System.out.println("DEP PREDS: " + depPredicates);
		// -------------------------------------
		Set<Term> unProvenCompPreds = new HashSet<>();
		for (Term pred : compPredicates) {
			System.out.println("Proving Comp Pred: " + pred);
			if (!sequentImpliesPredicate(pred)) {
				unProvenCompPreds.add(pred);
			}
		}
		compPredicates.removeAll(unProvenCompPreds);
		Set<Term> weakenedCompPreds = new HashSet<>();
		for (Term un : unProvenCompPreds) {
//			System.out.println("Weakening unproven: " + un);
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
//		**
//		System.out.println("Weaken " + unProven + ": ");
		if(unProven!=null) {
			result.addAll(weakenByPredicateSymbol(unProven));

		System.out.println("Weaken by Index for "+unProven);
			result.addAll(weakenByIndexesANDPredicate(unProven));
			if (itrNumber < 1) {
//			System.out.println("Weaken by Subset for "+unProven);
				if(innerLoop)
					result.addAll(weakenBySubSetInnerLoop(unProven));
				else
					result.addAll(weakenBySubSetOuterLoop(unProven, m));
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
		} else if (unProven.op().equals(depLDT.getNoW())) {
			result.add(tb.noRaW(unProven.sub(0)));
			result.add(tb.noWaR(unProven.sub(0)));
			result.add(tb.noWaW(unProven.sub(0)));
		}
		return result;
	}

	private Set<Term> weakenBySubSetInnerLoop(Term unProven) {
		Set<Term> result = new HashSet<>();
		final Term locSet = unProven.sub(0);

		if(locSet.op().equals(locsetLDT.getInfiniteUnion())) {
			weakenBySubSetInfiniteUnion(unProven);
		}
		else if (locSet.op().equals(locsetLDT.getArrayRange())) {
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
						result.add(tb.func(op, subLoc));
						result.add(tb.func(op, lowSingleton));
						result.add(tb.func(op, highSingleton));
					}
				}
			}
		}
		return result;
	}


	private Set<Term> weakenBySubSetOuterLoop(Term unProven, Term m) {
		Set<Term> result = new HashSet<>();
		final Term locSet = unProven.sub(0);

		if(locSet.op().equals(locsetLDT.getInfiniteUnion())) {
			weakenBySubSetInfiniteUnion(unProven);
		}
		else if (locSet.op().equals(locsetLDT.getArrayRange())) {
			final Term array = locSet.sub(0);
			final Term low = locSet.sub(1);
			final Term high = locSet.sub(2);
			final Term newLow = tb.add(low, m);
			final Term newHigh = tb.sub(high, m);

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
						result.add(tb.func(op, subLoc));
						result.add(tb.func(op, lowSingleton));
						result.add(tb.func(op, highSingleton));
					}
				}
			}
		}
		return result;
	}

	private Set<Term> weakenBySubSetInfiniteUnion(Term unProven) {
		Set<Term> result = new HashSet<>();
		final Term locSet = unProven.sub(0);

		final Term qVar = locSet.sub(0);
		final Term guard = locSet.sub(1);
		final Term arrRng = locSet.sub(2);

		final Term array = arrRng.sub(0);
		final Term inLow = arrRng.sub(1);
		final Term inHigh = arrRng.sub(2);

		Term outLow = tb.tt();
		Term outHigh = tb.tt();

		if(guard.sub(0).op() == intLDT.getGreaterOrEquals()){
			if(guard.sub(0).sub(0) == qVar)
				outLow = guard.sub(0).sub(1);
			else
				outHigh = guard.sub(0).sub(0);
		} else if (guard.sub(0).op() == intLDT.getLessOrEquals()) {
			if(guard.sub(0).sub(0) == qVar)
				outHigh = guard.sub(0).sub(1);
			else
				outLow = guard.sub(0).sub(0);
		}

		final Term newOutLow = tb.add(outLow, tb.one());
		final Term newOutHigh = tb.sub(outHigh, tb.one());

		if (!sProof.proofEquality(outLow, outHigh)) {
			final Term lowArr = tb.arrayRange(tb.dotArr(array, outLow), inLow, inHigh);
			final Term highArr = tb.arrayRange(tb.dotArr(array, outHigh), inLow, inHigh);

			Term subLoc;
			LogicVariable l = new LogicVariable(new Name("l"), intLDT.targetSort());
			if (sProof.proofLT(tb.zero(), newOutHigh)) {
				if (sProof.proofLT(newOutLow, newOutHigh)) {
					subLoc = tb.infiniteUnion(new QuantifiableVariable[]{l},tb.and(tb.geq(tb.var(l),newOutLow),tb.leq(tb.var(l), newOutHigh)),tb.arrayRange(tb.dotArr(array, tb.var(l)), inLow, inHigh));
				} else if (sProof.proofEquality(newOutLow, newOutHigh)) {
					subLoc = tb.arrayRange(tb.dotArr(array, newOutLow), inLow, inHigh);
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

		return result;
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

	private Set<Term> weakenByIndexesANDPredicate(Term pred){
		Set<Term> result = new HashSet<>();
		if(pred.sub(0).op() == locsetLDT.getArrayRange())
			result = weakenByIndexesANDPredicateOnArrayRange(pred);
		else if (pred.sub(0).op() == locsetLDT.getInfiniteUnion())
			result = weakenByIndexesANDPredicateOnInfiniteUnion(pred);

		return result;
	}

	private Set<Term> weakenByIndexesANDPredicateOnArrayRange(Term pred) {
		Set<Term> result = new HashSet<>();
		Term locSet = pred.sub(0);

		if (locSet != null) {
			System.out.println("Find Loc Set: "+locSet);
			Term array = locSet.sub(0);

			Term low = locSet.sub(1);
			Term high = locSet.sub(2);

			Term lowToInner, innerToHigh;
			Term lowToOuter, outerToHigh;
			System.out.println("low: "+ low + ", index: "+ indexInner + ", high: " + high);
			if(array == arrInner){
				if (!sProof.proofEquality(low, indexInner)) {
					if (!sProof.proofEquality(indexInner, high)) {
						lowToInner = tb.arrayRange(array, low, indexInner);
						innerToHigh = tb.arrayRange(array, indexInner, high);
//					if(sProof.proofLT(low, tb.subtract(index, tb.one())) && sProof.proofLT(tb.add(index, tb.one()), high)) {
//						lowToI = tb.arrayRange(array, low, tb.subtract(index, tb.one()));
//						iToHigh = tb.arrayRange(array, tb.add(index, tb.one()), high);
//					}
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
						final Function dependencyOp = (Function) pred.op();
						result.add(tb.func(dependencyOp, lowToInner));
						result.add(tb.func(dependencyOp, innerToHigh));
					}
				}
			}

			else if(array == arrOuter){
							System.out.println("low: "+ low + ", index: "+ indexOuter + ", high: " + high);
				if (!sProof.proofEquality(low, indexOuter)) {
					if (!sProof.proofEquality(indexOuter, high)) {
						lowToOuter = tb.arrayRange(array, low, indexOuter);
						outerToHigh = tb.arrayRange(array, indexOuter, high);
//					if(sProof.proofLT(low, tb.subtract(index, tb.one())) && sProof.proofLT(tb.add(index, tb.one()), high)) {
//						lowToI = tb.arrayRange(array, low, tb.subtract(index, tb.one()));
//						iToHigh = tb.arrayRange(array, tb.add(index, tb.one()), high);
//					}
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
						final Function dependencyOp = (Function) pred.op();
						result.add(tb.func(dependencyOp, lowToOuter));
						result.add(tb.func(dependencyOp, outerToHigh));
					}
				}
			}
			}

		System.out.println(result);
		return result;
	}

	private Set<Term> weakenByIndexesANDPredicateOnInfiniteUnion(Term pred) {
		Set<Term> result = new HashSet<>();
		Term locSet = pred.sub(0);

		if (locSet != null) {

			final Term qVar = locSet.sub(0);
			final Term guard = locSet.sub(1);
			final Term arrRng = locSet.sub(2);

			final Term array = arrRng.sub(0);
			final Term inLow = arrRng.sub(1);
			final Term inHigh = arrRng.sub(2);

			Term outLow = tb.tt();
			Term outHigh = tb.tt();

			if(guard.sub(0).op() == intLDT.getGreaterOrEquals()){
				if(guard.sub(0).sub(0) == qVar)
					outLow = guard.sub(0).sub(1);
				else
					outHigh = guard.sub(0).sub(0);
			} else if (guard.sub(0).op() == intLDT.getLessOrEquals()) {
				if(guard.sub(0).sub(0) == qVar)
					outHigh = guard.sub(0).sub(1);
				else
					outLow = guard.sub(0).sub(0);
			}

			LogicVariable l = new LogicVariable(new Name("l"), intLDT.targetSort());

			Term lowToInner, innerToHigh;
			Term lowToOuter, outerToHigh;
//			System.out.println("low: "+ low + ", index: "+ index + ", high: " + high);
			if (!sProof.proofEquality(outLow, indexInner)) {
				lowToInner = tb.infiniteUnion(new QuantifiableVariable[]{l},
						tb.and(tb.geq(tb.var(l),outLow),tb.leq(tb.var(l), indexInner)),
						tb.arrayRange(tb.dotArr(array, tb.var(l)), inLow, inHigh));
				if (!sProof.proofEquality(indexInner, outHigh)) {
					innerToHigh = tb.infiniteUnion(new QuantifiableVariable[]{l},tb.and(tb.geq(tb.var(l),indexInner),tb.leq(tb.var(l), outHigh)),tb.arrayRange(tb.dotArr(array, tb.var(l)), inLow, inHigh));
				} else {
					innerToHigh = tb.arrayRange(tb.dotArr(array, indexInner), inLow, inHigh);
				}
			} else {
				lowToInner = tb.arrayRange(tb.dotArr(array, indexInner), inLow, inHigh);
				if (!sProof.proofEquality(indexInner, outHigh)) {
					innerToHigh = tb.infiniteUnion(new QuantifiableVariable[]{l},tb.and(tb.geq(tb.var(l),indexInner),tb.leq(tb.var(l), outHigh)),tb.arrayRange(tb.dotArr(array, tb.var(l)), inLow, inHigh));
				} else {
					innerToHigh = tb.arrayRange(tb.dotArr(array, indexInner), inLow, inHigh);
				}
			}
			if (lowToInner != null && innerToHigh != null) {
				if (depLDT.isDependencePredicate(pred.op())) {
					final Function dependencyOp = (Function) pred.op();
					result.add(tb.func(dependencyOp, lowToInner));
					result.add(tb.func(dependencyOp, innerToHigh));
				}
			}
			//			System.out.println("low: "+ low + ", index: "+ index + ", high: " + high);
			if (!sProof.proofEquality(outLow, indexOuter)) {
				lowToOuter = tb.infiniteUnion(new QuantifiableVariable[]{l},tb.and(tb.geq(tb.var(l),outLow),tb.leq(tb.var(l), indexOuter)),tb.arrayRange(tb.dotArr(array, tb.var(l)), inLow, inHigh));
				if (!sProof.proofEquality(indexOuter, outHigh)) {
					outerToHigh = tb.infiniteUnion(new QuantifiableVariable[]{l},tb.and(tb.geq(tb.var(l),indexOuter),tb.leq(tb.var(l), outHigh)),tb.arrayRange(tb.dotArr(array, tb.var(l)), inLow, inHigh));
				} else {
					outerToHigh = tb.arrayRange(tb.dotArr(array, indexOuter), inLow, inHigh);
				}
			} else {
				lowToOuter = tb.arrayRange(tb.dotArr(array, indexOuter), inLow, inHigh);
				if (!sProof.proofEquality(indexOuter, outHigh)) {
					outerToHigh = tb.infiniteUnion(new QuantifiableVariable[]{l},tb.and(tb.geq(tb.var(l),indexOuter),tb.leq(tb.var(l), outHigh)),tb.arrayRange(tb.dotArr(array, tb.var(l)), inLow, inHigh));
				} else {
					outerToHigh = tb.arrayRange(tb.dotArr(array, indexOuter), inLow, inHigh);
				}
			}
			if (lowToOuter != null && outerToHigh != null) {
				if (depLDT.isDependencePredicate(pred.op())) {
					final Function dependencyOp = (Function) pred.op();
					result.add(tb.func(dependencyOp, lowToOuter));
					result.add(tb.func(dependencyOp, outerToHigh));
				}
			}
		}

//		System.out.println(result);
		return result;
	}


	private Set<Term> weakeningComparisonPredicates(Term pred) {
		Set<Term> result = new HashSet<>();
		if(pred!=null) {
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
//		System.out.println(result);
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
//		System.out.println(result);
		return result;
	}
}