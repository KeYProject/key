package de.uka.ilkd.key.loopinvgen;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.DependenciesLDT;
import de.uka.ilkd.key.ldt.IntegerLDT;
import de.uka.ilkd.key.ldt.LocSetLDT;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.Equality;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.prover.impl.ApplyStrategyInfo;
import de.uka.ilkd.key.util.Pair;

import java.util.HashSet;
import java.util.Set;

public class PredicateRefinementNew3 {

	public Set<Term> refinedCompList;
	public Set<Term> refinedDepList;

	private final Sequent seq;
	private Set<Term> depPredicates = new HashSet<>();
	private Set<Term> compPredicates = new HashSet<>();
	private final Services services;
	private SideProof sProof;
	private final DependenciesLDT depLDT;
	private final LocSetLDT locsetLDT;
	private final TermBuilder tb;
	private final Term index;
	private final IntegerLDT intLDT;
	private final int itrNumber;

	public PredicateRefinementNew3(Services s, Sequent sequent, Set<Term> depPredList, Set<Term> compPredList, Term i,
			int itr) {
		services = s;
		depPredicates = depPredList;
		compPredicates = compPredList;
		depLDT = services.getTypeConverter().getDependenciesLDT();
		locsetLDT = services.getTypeConverter().getLocSetLDT();
		tb = services.getTermBuilder();
		index = i;
		intLDT = services.getTypeConverter().getIntegerLDT();
		itrNumber = itr;
		//seq = filter(sequent);
		seq=simplify(filter(sequent));
		sProof = new SideProof(services, seq);
	}

	private Sequent simplify(Sequent sequent) {
		try {
			ApplyStrategyInfo info = SideProof.isProvableHelper(sequent, 1000, true, false, services);
			if (info.getProof().openGoals().size() != 1) {
				throw new ProofInputException("Illegal number of goals. Open goals: " + info.getProof().openGoals().size());
			}
			sequent = info.getProof().openGoals().head().sequent();
		} catch (ProofInputException e) {
			e.printStackTrace();
		}
		return sequent;
	}

	private Sequent filter(Sequent originalSequent) {
		Sequent sequent = Sequent.EMPTY_SEQUENT;

		for (SequentFormula sequentFormula : originalSequent.antecedent()) {
			sequent = sequent.addFormula(sequentFormula, true, false).sequent();
		}

		for (SequentFormula sequentFormula : originalSequent.succedent()) {
			if (!sequentFormula.formula().containsJavaBlockRecursive()) {
				sequent = sequent.addFormula(sequentFormula, false, false).sequent();
			}
		}
		return sequent;
	}

	public Pair<Set<Term>, Set<Term>> predicateCheckAndRefine() {
		Set<Term> unProvenDepPreds = new HashSet<>();
		for (Term pred : depPredicates) {
//	**				
			System.out.println("Proving Dep Pred: " + pred);
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
			for (Term dp : depPredicates) {
				if (predicateImpliedBypredicate(w, dp)) {
//					**		
					System.out.println("IMPLIED " + w + " by " + dp);
					break;
				}
			}
			if (!depPredicates.contains(w)) {
				if (sequentImpliesPredicate(w)) {
					depPredicates.add(w);
				}
			}
		}
//		System.out.println("DEP PREDS: " + depPredicates);
		// -------------------------------------
		Set<Term> unProvenCompPreds = new HashSet<>();
		for (Term pred : compPredicates) {
//			System.out.println("Proving Comp Pred: " + pred);
			if (!sequentImpliesPredicate(pred)) {
//				System.out.println("not proved: "+pred);
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

	private boolean predicateImpliedBypredicate(Term dp1, Term dp2) {
		if (dp1.op() == dp2.op() && sProof.proofSubSet(dp1.sub(0), dp2.sub(0))) {
			return true;
		} else if (dp2.op().equals(depLDT.getNoR())) {
			if (dp1.op().equals(depLDT.getNoRaW()) || dp1.op().equals(depLDT.getNoWaR())) {
				if (sProof.proofSubSet(dp1.sub(0), dp2.sub(0))) {
					return true;
				}
			}
		} else if (dp2.op().equals(depLDT.getNoW())) {
			if (dp1.op().equals(depLDT.getNoRaW()) || dp1.op().equals(depLDT.getNoWaR())
					|| dp1.op().equals(depLDT.getNoWaW())) {
				if (sProof.proofSubSet(dp1.sub(0), dp2.sub(0))) {
					return true;
				}
			}
		}
		return false;
	}

	private boolean sequentImpliesPredicate(Term pred) {
//		**		
		System.out.println("sequentImpliesPredicate is called for: "+pred);
		Sequent sideSeq = seq.addFormula(new SequentFormula(pred), false, true).sequent();

//		System.out.println("is Provable called for: " +  pred);
		final boolean provable = SideProof.isProvable(sideSeq, 100000, true, services);
//		if (!provable && (pred.op() == intLDT.getLessThan() || pred.op() == intLDT.getLessOrEquals()
//				|| pred.op() == intLDT.getGreaterThan() || pred.op() == intLDT.getGreaterOrEquals()
//				|| pred.op() == Equality.EQUALS)) {//
//			System.out.println("NOT Proved: " + ProofSaver.printAnything(sideSeq, services));
//		}
//		else if (provable && pred.op() == services.getTypeConverter().getDependenciesLDT().getNoR()) {
//			System.out.println("Check: " + ProofSaver.printAnything(sideSeq, services));
//		}
//		System.out.println("Proof " + pred + ":  "+ provable);// + " in the following seq:");
//		System.out.println(sideSeq);
//		System.out.println("---------------------------------------------------------------");
//		if (!provable && pred.op() == services.getTypeConverter().getDependenciesLDT().getNoWaW()) {
//			System.out.println("We have a Problem" );
//		}
//		**	
		System.out.println(provable);
		return provable;
	}

	private Set<Term> weakeningDependencePredicates(Term unProven) {
		Set<Term> result = new HashSet<>();
//		**		
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
		return result;
	}

	private Set<Term> weakenByPredicateSymbol(Term unProven) {
		Set<Term> result = new HashSet<>();
//		if (unProven.sub(0) != locsetLDT.getEmpty()) {
		if (unProven.op().equals(depLDT.getNoR())) {
			result.add(tb.noRaW(unProven.sub(0)));
			result.add(tb.noWaR(unProven.sub(0)));
		} else if (unProven.op().equals(depLDT.getNoW())) {
			result.add(tb.noRaW(unProven.sub(0)));
			result.add(tb.noWaR(unProven.sub(0)));
			result.add(tb.noWaW(unProven.sub(0)));
		}
//		}
//		System.out.println(result);
		return result;
	}

	private Set<Term> weakenBySubSetOLD(Term unProven) {
		Set<Term> result = new HashSet<>();
		final Term locSet = unProven.sub(0);
		Term lowSingleton = null;
		Term highSingleton = null;
		Term subLoc = null;

//		Term opOnSubLocs = null;
		if (!locSet.equals(locsetLDT.getEmpty()) && locSet != null && locSet.op().equals(locsetLDT.getArrayRange())) {
			final Term array = locSet.sub(0);
			final Term low = locSet.sub(1);
			final Term newLow = tb.add(low, tb.one());
			final Term high = locSet.sub(2);
			final Term newHigh = tb.sub(high, tb.one());

			if (sProof.proofLEQ(low, high)) {
				lowSingleton = tb.singleton(array, tb.arr(low));
				highSingleton = tb.singleton(array, tb.arr(high));
				if (sProof.proofEquality(newLow, newHigh))
					subLoc = tb.singleton(array, tb.arr(newLow));
				else
					subLoc = tb.arrayRange(array, newLow, newHigh);

				if (unProven.op().equals(depLDT.getNoR())) {
					result.add(tb.noR(subLoc));
					result.add(tb.noR(lowSingleton));
					result.add(tb.noR(highSingleton));
				} else if (unProven.op().equals(depLDT.getNoW())) {
					result.add(tb.noW(subLoc));
					result.add(tb.noW(lowSingleton));
					result.add(tb.noW(highSingleton));
				} else if (unProven.op().equals(depLDT.getNoRaW())) {
					result.add(tb.noRaW(subLoc));
					result.add(tb.noRaW(lowSingleton));
					result.add(tb.noRaW(highSingleton));
				} else if (unProven.op().equals(depLDT.getNoWaR())) {
					result.add(tb.noWaR(subLoc));
					result.add(tb.noWaR(lowSingleton));
					result.add(tb.noWaR(highSingleton));
				} else if (unProven.op().equals(depLDT.getNoWaW())) {
					result.add(tb.noWaW(subLoc));
					result.add(tb.noWaW(lowSingleton));
					result.add(tb.noWaW(highSingleton));
				}
			}
		}
//		System.out.println(result);
		return result;
	}

	private Set<Term> weakenBySubSet(Term unProven) {
		Set<Term> result = new HashSet<>();
		final Term locSet = unProven.sub(0);
		Term lowSingleton = null;
		Term highSingleton = null;
		Term subLoc = null;

//		Term opOnSubLocs = null;
		if (!locSet.equals(locsetLDT.getEmpty()) && locSet != null && locSet.op().equals(locsetLDT.getArrayRange())) {
			final Term array = locSet.sub(0);
			final Term low = locSet.sub(1);
			final Term newLow = tb.add(low, tb.one());
			final Term high = locSet.sub(2);
			final Term newHigh = tb.sub(high, tb.one());

			if (!sProof.proofEquality(low, high)) {
				lowSingleton = tb.singleton(array, tb.arr(low));
				highSingleton = tb.singleton(array, tb.arr(high));

				if (sProof.proofLT(tb.zero(), newHigh)) {
					if (sProof.proofLT(newLow, newHigh)) {
						subLoc = tb.arrayRange(array, newLow, newHigh);
					} else if (sProof.proofEquality(newLow, newHigh)) {
						subLoc = tb.singleton(array, tb.arr(newLow));
					}
					if (unProven.op().equals(depLDT.getNoR())) {
						result.add(tb.noR(subLoc));
						result.add(tb.noR(lowSingleton));
						result.add(tb.noR(highSingleton));
					} else if (unProven.op().equals(depLDT.getNoW())) {
						result.add(tb.noW(subLoc));
						result.add(tb.noW(lowSingleton));
						result.add(tb.noW(highSingleton));
					} else if (unProven.op().equals(depLDT.getNoRaW())) {
						result.add(tb.noRaW(subLoc));
						result.add(tb.noRaW(lowSingleton));
						result.add(tb.noRaW(highSingleton));
					} else if (unProven.op().equals(depLDT.getNoWaR())) {
						result.add(tb.noWaR(subLoc));
						result.add(tb.noWaR(lowSingleton));
						result.add(tb.noWaR(highSingleton));
					} else if (unProven.op().equals(depLDT.getNoWaW())) {
						result.add(tb.noWaW(subLoc));
						result.add(tb.noWaW(lowSingleton));
						result.add(tb.noWaW(highSingleton));
					}
				}
			}
		}
//		System.out.println(result);
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

	private Set<Term> weakenByIndexANDPredicate(Term pred) {
		Set<Term> result = new HashSet<>();
		Term locSet = findArrayRange(pred.sub(0));

		if (locSet != null) {
//			System.out.println("Find Loc Set: "+locSet);
			Term array = locSet.sub(0);
			Term low = locSet.sub(1);
			Term high = locSet.sub(2);
			Term lowToI = null;
			Term iToHigh = null;
//			System.out.println("low: "+ low + ", index: "+ index + ", high: " + high);
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
				if (pred.op() == depLDT.getNoR()) {
					result.add(tb.noR(lowToI));
					result.add(tb.noR(iToHigh));
				} else if (pred.op() == depLDT.getNoW()) {
					result.add(tb.noW(lowToI));
					result.add(tb.noW(iToHigh));
				} else if (pred.op() == depLDT.getNoRaW()) {
					result.add(tb.noRaW(lowToI));
					result.add(tb.noRaW(iToHigh));
				} else if (pred.op() == depLDT.getNoWaR()) {
					result.add(tb.noWaR(lowToI));
					result.add(tb.noWaR(iToHigh));
				} else if (pred.op() == depLDT.getNoWaW()) {
					result.add(tb.noWaW(lowToI));
					result.add(tb.noWaW(iToHigh));
				}
			}
		}
//		System.out.println(result);
		return result;
	}

	private Set<Term> weakeningComparisonPredicates(Term pred) {
		Set<Term> result = new HashSet<>();
//		result.addAll(compPredWeakenByIndex(pred));
//		System.out.println("Weakening by Predicate for: " + pred);
		result.addAll(compPredWeakeningByPredicates(pred));
//		System.out.println("Weakening by Heuristics for: " + pred);
		if (itrNumber < 1)
			result.addAll(compPredWeakeningByHeuristics(pred));
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
		return result;
	}

	private Set<Term> compPredWeakeningByHeuristics(Term pred) {

		Set<Term> result = new HashSet<>();
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
//		System.out.println(result);
		return result;
	}
}