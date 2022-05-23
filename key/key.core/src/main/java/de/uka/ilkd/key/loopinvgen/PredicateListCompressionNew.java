package de.uka.ilkd.key.loopinvgen;

import java.util.HashSet;
import java.util.Set;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.DependenciesLDT;
import de.uka.ilkd.key.ldt.IntegerLDT;
import de.uka.ilkd.key.ldt.LocSetLDT;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.Equality;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.Operator;

public class PredicateListCompressionNew {
	private final DependenciesLDT depLDT;
	private final Services services;
	private final TermBuilder tb;
	private final Sequent seq;
//	private final SequentFormula currentIdxF;
	private final IntegerLDT intLDT;
	private final Set<Operator> CompOps = new HashSet<>();
	private final Function lt, leq, gt, geq;
	private SideProof sProof;
	private final boolean ailias;
	private Set<Term> allPreds = new HashSet<>();
	private LocSetLDT locSetLDT;

	public PredicateListCompressionNew(Services s, Sequent sequent, Set<Term> preds, boolean ailiasing) {
		services = s;
		tb = services.getTermBuilder();
		seq = sequent;
//		currentIdxF = currentIndexFormula;
		depLDT = services.getTypeConverter().getDependenciesLDT();

		intLDT = services.getTypeConverter().getIntegerLDT();
		lt = intLDT.getLessThan();
		CompOps.add(lt);
		leq = intLDT.getLessOrEquals();
		CompOps.add(leq);
		gt = intLDT.getGreaterThan();
		CompOps.add(gt);
		geq = intLDT.getGreaterOrEquals();
		CompOps.add(geq);
		sProof = new SideProof(services, seq, 75000);
		ailias = ailiasing;
		allPreds = preds;
		locSetLDT = new LocSetLDT(services);
	}

	public Set<Term> compression() {

		Set<Term> compPredsList = new HashSet<>();
		Set<Term> depPredsList = new HashSet<>();
		Set<Term> result = new HashSet<>();
		for (Term term : allPreds) {
			if (term.op().equals(depLDT.getNoR()) || term.op().equals(depLDT.getNoW())
					|| term.op().equals(depLDT.getNoRaW()) || term.op().equals(depLDT.getNoWaR())
					|| term.op().equals(depLDT.getNoWaW())) {
				depPredsList.add(term);
			} else if (term.op().equals(lt) || term.op().equals(leq) || term.op().equals(gt) || term.op().equals(geq)
					|| term.op().equals(Equality.EQUALS)) {
				compPredsList.add(term);
			} else
				result.add(term);
		}
		result.addAll(finalCompPredListCompression(compPredsList));
//		result.addAll(compPredsList);
		result.addAll(depPredListCompressionByPredicate(depPredListCompressionBySET(depPredsList)));
		return result;

	}

	private Set<Term> depPredListCompressionBySET(Set<Term> fDepPredList) {
		Set<Term> toDelete = new HashSet<>();
		Set<Term> toAdd = new HashSet<>();
		for (Term depPred1 : fDepPredList) {
			for (Term depPred2 : fDepPredList) {
				if (depPred1.op() == depPred2.op() && depPred1.sub(0) != depPred2.sub(0)) {
					if (sProof.proofSubSet(depPred1.sub(0), depPred2.sub(0))) {
						toDelete.add(depPred1);
					}
//					else if(sProof.proofSubSet(depPred2.sub(0), depPred1.sub(0)) && depPred1.sub(0)!=depPred2.sub(0)){
//						toDelete.add(depPred2);
//					} 
					else if (depPred1.sub(0).op() == locSetLDT.getArrayRange()
							&& depPred2.sub(0).op() == locSetLDT.getArrayRange()) {
						if (depPred1.sub(0).sub(0) == depPred2.sub(0).sub(0)
								&& depPred1.sub(0).sub(2) == depPred2.sub(0).sub(1)) {
							toDelete.add(depPred1);
							toDelete.add(depPred2);
							if (depPred1.op() == depLDT.getNoR()) {
								toAdd.add(tb.noR(tb.arrayRange(depPred1.sub(0).sub(0), depPred1.sub(0).sub(1),
										depPred2.sub(0).sub(2))));
							} else if (depPred1.op() == depLDT.getNoRaW()) {
								toAdd.add(tb.noRaW(tb.arrayRange(depPred1.sub(0).sub(0), depPred1.sub(0).sub(1),
										depPred2.sub(0).sub(2))));
							} else if (depPred1.op() == depLDT.getNoWaR()) {
								toAdd.add(tb.noWaR(tb.arrayRange(depPred1.sub(0).sub(0), depPred1.sub(0).sub(1),
										depPred2.sub(0).sub(2))));
							} else if (depPred1.op() == depLDT.getNoWaW()) {
								toAdd.add(tb.noWaW(tb.arrayRange(depPred1.sub(0).sub(0), depPred1.sub(0).sub(1),
										depPred2.sub(0).sub(2))));
							} else if (depPred1.op() == depLDT.getNoW()) {
								toAdd.add(tb.noW(tb.arrayRange(depPred1.sub(0).sub(0), depPred1.sub(0).sub(1),
										depPred2.sub(0).sub(2))));
							}
						}
					}
				}
			}
		}
		fDepPredList.addAll(toAdd);
		fDepPredList.removeAll(toDelete);
		
		toDelete.removeAll(toDelete);
		if (ailias) {
			for (Term depPred1 : fDepPredList) {
				for (Term depPred2 : fDepPredList) {
					if (depPred1.op().equals(depPred2.op()) && depPred1.sub(0).sub(0) != depPred2.sub(0).sub(0)) {
						if (sProof.proofEquality(depPred1.sub(0), depPred2.sub(0))) {
							if (!toDelete.contains(depPred2)) {
								toDelete.add(depPred1);
							}
						}
					}
				}
			}
		}

		return fDepPredList;
	}

	private Set<Term> depPredListCompressionByPredicate(Set<Term> fDepPredList) {
		Set<Term> toDelete = new HashSet<>();
		for (Term depPred1 : fDepPredList) {
			for (Term depPred2 : fDepPredList) {
				if (depPred1.op().equals(depLDT.getNoR())) {
					if (depPred2.op().equals(depLDT.getNoRaW()) || depPred2.op().equals(depLDT.getNoWaR())) {
						if (sProof.proofSubSet(depPred2.sub(0), depPred1.sub(0))) {
							toDelete.add(depPred2);
						}
					}
				} else if (depPred1.op().equals(depLDT.getNoW())) {
					if (depPred2.op().equals(depLDT.getNoRaW()) || depPred2.op().equals(depLDT.getNoWaR())
							|| depPred2.op().equals(depLDT.getNoWaW())) {
						if (sProof.proofSubSet(depPred2.sub(0), depPred1.sub(0))) {
							toDelete.add(depPred2);
						}
					}
				}
			}
		}
		fDepPredList.removeAll(toDelete);
		return fDepPredList;
	}

	private Set<Term> finalCompPredListCompression(Set<Term> fCompPredList) {
		Set<Term> toDelete = new HashSet<>();
		Set<Term> toAdd = new HashSet<>();
		for (Term compPred1 : fCompPredList) {
			for (Term compPred2 : fCompPredList) {
				if (sProof.proofEquality(compPred1.sub(0), compPred2.sub(0))
						&& sProof.proofEquality(compPred1.sub(1), compPred2.sub(1))) { // a X b
					// && a
					// Y b
					if (compPred1.op().equals(geq) && compPred2.op().equals(gt)) {
						if (!toDelete.contains(compPred1)) {
							toDelete.add(compPred2);
						}
					} else if (compPred1.op().equals(leq) && compPred2.op().equals(lt)) {
						if (!toDelete.contains(compPred1)) {
							toDelete.add(compPred2);
						}
					} else if (compPred1.op().equals(Equality.EQUALS) && compPred2.op().equals(geq)) {
						if (!toDelete.contains(compPred2)) {
							toDelete.add(compPred1);
						}
					} else if (compPred1.op().equals(Equality.EQUALS) && compPred2.op().equals(leq)) {
						if (!toDelete.contains(compPred2)) {
							toDelete.add(compPred1);
						}
					}
//					else if (compPred1.op().equals(gt) && compPred2.op().equals(lt)) { //There should not be such a case because this means the inv is wrong
//						toDelete.add(compPred1);
//						toDelete.add(compPred2);
//					}
					else if (compPred1.op().equals(geq) && compPred2.op().equals(leq)) {
						toDelete.add(compPred1);
						toDelete.add(compPred2);
						toAdd.add(tb.equals(compPred1.sub(0), compPred1.sub(1)));
					}

				} else if (sProof.proofEquality(compPred1.sub(0), compPred2.sub(1))
						&& sProof.proofEquality(compPred1.sub(1), compPred2.sub(0))) { // a
					// X
					// b
					// &&
					// b
					// Y
					// a
					if (compPred1.op().equals(gt) && compPred2.op().equals(lt)) {
						if (!toDelete.contains(compPred2)) {
							toDelete.add(compPred1);
						}
					} else if (compPred1.op().equals(geq) && compPred2.op().equals(lt)) {
						if (!toDelete.contains(compPred1)) {
							toDelete.add(compPred2);
						}
					} else if (compPred1.op().equals(leq) && compPred2.op().equals(gt)) {
						if (!toDelete.contains(compPred1)) {
							toDelete.add(compPred2);
						}
					} else if (compPred1.op().equals(geq) && compPred2.op().equals(leq)) {
						if (!toDelete.contains(compPred2)) {
						toDelete.add(compPred1);
						}
					} else if (compPred1.op().equals(Equality.EQUALS) && compPred2.op().equals(geq)) {
						if (!toDelete.contains(compPred2)) {
							toDelete.add(compPred1);
						}
					} else if (compPred1.op().equals(Equality.EQUALS) && compPred2.op().equals(leq)) {
						if (!toDelete.contains(compPred2)) {
							toDelete.add(compPred1);
						}
					}
				} else if (sProof.proofEquality(compPred1.sub(0), compPred2.sub(0))
						&& !sProof.proofEquality(compPred1.sub(1), compPred2.sub(1))) {
					if ((compPred1.op() == lt && compPred2.op() == lt)
							|| (compPred1.op() == lt && compPred2.op() == leq)) {
						if (sProof.proofLT(compPred1.sub(1), compPred2.sub(1))) {
							if (!toDelete.contains(compPred2)) {
								toDelete.add(compPred1);
							}
						} else {
							if (!toDelete.contains(compPred1)) {
								toDelete.add(compPred2);
							}
						}
					} else if ((compPred1.op() == gt && compPred2.op() == gt)
							|| (compPred1.op() == gt && compPred2.op() == geq)) {
						if (sProof.proofLT(compPred1.sub(1), compPred2.sub(1))) {
							if (!toDelete.contains(compPred1)) {
								toDelete.add(compPred2);
							}
						} else {
							if (!toDelete.contains(compPred2)) {
								toDelete.add(compPred1);
							}
						}
					} else if ((compPred1.op() == leq && compPred2.op() == leq)
							|| (compPred1.op() == leq && compPred2.op() == lt)) {
						if (sProof.proofLT(compPred1.sub(1), compPred2.sub(1))) {
							if (!toDelete.contains(compPred2)) {
								toDelete.add(compPred1);
							}
						} else {
							if (!toDelete.contains(compPred1)) {
								toDelete.add(compPred2);
							}
						}
					}
				} else if ((compPred1.op() == geq && compPred2.op() == geq)
						|| (compPred1.op() == gt && compPred2.op() == gt)) {
					if (sProof.proofLT(compPred1.sub(1), compPred2.sub(1))) {
						if (!toDelete.contains(compPred1)) {
							toDelete.add(compPred2);
						}
					} else {
						if (!toDelete.contains(compPred2)) {
							toDelete.add(compPred1);
						}
					}

				} else if (compPred1.op() == compPred2.op() && sProof.proofEquality(compPred1.sub(1), compPred2.sub(1))
						&& !sProof.proofEquality(compPred1.sub(0), compPred2.sub(0))) {
					if (compPred1.op() == lt) {
						if (sProof.proofLT(compPred1.sub(0), compPred2.sub(0))) {
							if (!toDelete.contains(compPred2)) {
								toDelete.add(compPred1);
							}
						} else {
							if (!toDelete.contains(compPred1)) {
								toDelete.add(compPred2);
							}
						}
					} else if (compPred1.op() == gt) {
						if (sProof.proofLT(compPred1.sub(0), compPred2.sub(0))) {
							if (!toDelete.contains(compPred1)) {
								toDelete.add(compPred2);
							}
						} else {
							if (!toDelete.contains(compPred2)) {
								toDelete.add(compPred1);
							}
						}
					} else if (compPred1.op() == leq) {
						if (sProof.proofLT(compPred1.sub(0), compPred2.sub(0))) {
							if (!toDelete.contains(compPred2)) {
								toDelete.add(compPred1);
							}
						} else {
							if (!toDelete.contains(compPred1)) {
								toDelete.add(compPred2);
							}
						}
					} else if (compPred1.op() == geq) {
						if (sProof.proofLT(compPred1.sub(0), compPred2.sub(0))) {
							if (!toDelete.contains(compPred1)) {
								toDelete.add(compPred2);
							}
						} else {
							if (!toDelete.contains(compPred2)) {
								toDelete.add(compPred1);
							}
						}
					}
				}
			}
		}
		fCompPredList.removeAll(toDelete);
//		System.out.println("deleted by compression: " + toDelete);
		return fCompPredList;
	}
}
