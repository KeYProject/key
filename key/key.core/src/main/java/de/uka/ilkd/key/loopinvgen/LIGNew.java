package de.uka.ilkd.key.loopinvgen;

import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.Statement;
import de.uka.ilkd.key.java.expression.operator.*;
import de.uka.ilkd.key.java.statement.While;
import de.uka.ilkd.key.ldt.IntegerLDT;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.ArraySort;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.util.Pair;
import org.key_project.util.collection.ImmutableList;

import java.util.HashSet;
import java.util.Set;

public class LIGNew {

	private final Sequent seq;
	private final Services services;
	private final TermBuilder tb;
	private Term low, high, index, guard;
	private Set<Term> arrays = new HashSet<>();
	private final RuleApplication ruleApp;
	private Set<Term> oldDepPreds = new HashSet<>();
	private Set<Term> allDepPreds = new HashSet<>();
	private Set<Term> oldCompPreds = new HashSet<>();
	private Set<Term> allCompPreds = new HashSet<>();
	private final IntegerLDT intLDT;
	public LIGNew(Services s, Sequent sequent) {
		seq = sequent;
		ruleApp = new RuleApplication(s, seq);
		services = ruleApp.services;
		tb = services.getTermBuilder();
		intLDT = services.getTypeConverter().getIntegerLDT();
	}
	
	public void mainAlg() {
		getLow(seq);
		getIndexAndHigh(seq);
		getLocSet(seq);

		
		for (SequentFormula sf : seq.antecedent()) {
			if (!sf.formula().containsJavaBlockRecursive() && isComparisonOperator(sf.formula())) {
				allCompPreds.add(sf.formula());
			}
		}
		for (SequentFormula sf : seq.succedent()) {
			if (!sf.formula().containsJavaBlockRecursive() && isComparisonOperator(sf.formula())) {
				allCompPreds.add(tb.not(sf.formula()));
			}
		}

//		System.out.println("Goals before shift number -1: "+services.getProof().openGoals());
		ImmutableList<Goal> goalsAfterShift = ruleApp.applyShiftUpdateRule(services.getProof().openGoals());
//		System.out.println("SHIFTED");
//		System.out.println("number of goals after shift number -1: " + goalsAfterShift.size());// It is always one
//		System.out.println(
//				"Goals after shift -1: " + ProofSaver.printAnything(goalsAfterShift.head().sequent(), services));
		ImmutableList<Goal> goalsAfterUnwind = null;

		Goal currentGoal = goalsAfterShift.head();// Number of goals after shift does not change

		
//		// Initial Predicate Sets for stencil and conditionalWithDifferentEvents: 
//		allCompPreds.add(tb.geq(index, tb.sub(low,tb.one())));//
//		allCompPreds.add(tb.leq(index, tb.add(high, tb.one())));//
//		for (Term arr : arrays) {
//			allDepPreds.add(tb.noR(tb.arrayRange(arr, tb.sub(low,tb.one()), high)));
//			allDepPreds.add(tb.noW(tb.arrayRange(arr, tb.sub(low,tb.one()), high)));
//		}
		
		
//		//Initial Predicate Sets for shiftArrayToLeft, shiftArrayToLeftWithBreak, withoutFunc, withFunc, conditionWithDifferentNumberOfEvent, condition:
		allCompPreds.add(tb.geq(index, low));
		allCompPreds.add(tb.leq(index, tb.add(high,tb.one())));
		for (Term arr : arrays) {
			allDepPreds.add(tb.noR(tb.arrayRange(arr, low, high)));
			allDepPreds.add(tb.noW(tb.arrayRange(arr, low, high)));
		}
		
		

//		System.out.println("Initial comp Predicate Set: " + allCompPreds);
//		for (Term term : allPreds) {
//			System.out.println(term);
//		}
		int itrNumber = -1;
		PredicateRefinementNew3 pr0 = new PredicateRefinementNew3(currentGoal.sequent(), allDepPreds, allCompPreds,
				index, itrNumber, services);
		Pair<Set<Term>, Set<Term>> refinedPreds = pr0.predicateCheckAndRefine();
//		System.out.println(ProofSaver.printAnything(seq, services));
		allDepPreds = refinedPreds.first;
		allCompPreds = refinedPreds.second;

//		for (Goal g : goalsAfterShift) {
//			g = abstractGoal(g);
//		}

		do {
			itrNumber++;
//			**		
			System.out.println("Iteration Number: " + itrNumber);

			oldDepPreds.clear();
			oldCompPreds.clear();

			oldDepPreds.addAll(allDepPreds);
			oldCompPreds.addAll(allCompPreds);

//			System.out.println("BEFORE UNWIND");
//			System.out.println(goalsAfterShift);
//			System.out.println("Goals Before Unwind:" + goalsAfterShift);

			goalsAfterUnwind = ruleApp.applyUnwindRule(goalsAfterShift);
//			System.out.println("AFTER UNWIND");
//			System.out.println("Number of goals after unwind: " + goalsAfterUnwind.size());
//			System.out.println("Goals After Unwind:" + goalsAfterUnwind);
//			System.out.println(goalsAfterUnwind);
			goalsAfterShift = ruleApp.applyShiftUpdateRule(goalsAfterUnwind);
//			System.out.println("SHIFT");
//			System.out.println("Number of goals after shift: " + goalsAfterShift.size());
//			System.out.println("Goals After Shift:" + goalsAfterShift);

			currentGoal = ruleApp.findLoopUnwindTacletGoal(goalsAfterShift);

//			System.out.println("Current Goal: " + currentGoal);
//			currentIndexFormula = currentIndexEq(currentGoal.sequent(), index);
//			System.out.println("Before refinement: " + currentGoal.sequent());

			PredicateRefinementNew3 pr = new PredicateRefinementNew3(currentGoal.sequent(), allDepPreds, allCompPreds,
					index, itrNumber, services);
			refinedPreds = pr.predicateCheckAndRefine();
			allDepPreds = refinedPreds.first;
			allCompPreds = refinedPreds.second;
			
//			currentGoal = abstractGoal(currentGoal);
			for (Goal g : goalsAfterShift) {
				g = abstractGoal(g);
			}
//			System.out.println("Dep Preds: " + allDepPreds);
		} while ((!allCompPreds.equals(oldCompPreds) || !allDepPreds.equals(oldDepPreds)) || itrNumber < 2);

//		System.out.println("===========Terminated===========");
//		System.out.println("Number of iterations at the end: " + itrNumber);
//		System.out.println("LIG is the conjunction of: ");
//		for (Term term : allDepPreds) {
//			System.out.println(term);
//		}
//		for (Term term : allCompPreds) {
//			System.out.println(term);
//		}
//		System.out.println(" of size " + allDepPreds.size() + " plus " + allCompPreds.size());
		
		allDepPreds.addAll(allCompPreds);

//		System.out.println("Without compression, the DD LOOP INVARIANT is the conjunction of: ");
//		for (Term term : allDepPreds) {
//			System.out.println(term);
//		}

		PredicateListCompressionNew plcDep = new PredicateListCompressionNew(services, currentGoal.sequent(), allDepPreds, false);
		allDepPreds = plcDep.compression();
		System.out.println("After compression, the DD LOOP INVARIANT is the conjunction of: ");
		for (Term term : allDepPreds) {
				System.out.println(term);
		}
		System.out.println("after " + itrNumber + " iterations of the LIG algorithm");
	}

	private Goal abstractGoal(Goal currentGoal) {
//		System.out.println("Goal: " + currentGoal);
		for (SequentFormula cgsf : currentGoal.sequent().antecedent()) {
			PosInOccurrence p = new PosInOccurrence(cgsf, PosInTerm.getTopLevel(), true);
			currentGoal.removeFormula(p);
		}

		for(SequentFormula cgsf:currentGoal.sequent().succedent()) {
			PosInOccurrence p = new PosInOccurrence(cgsf, PosInTerm.getTopLevel(), false);
			if(!cgsf.formula().containsJavaBlockRecursive()) {
				currentGoal.removeFormula(p);
			}
		}

		for (Term cp : allCompPreds) {
			currentGoal.addFormula(new SequentFormula(cp), true, false);
//			currentGoal.addFormula(new SequentFormula(cp), false, false);
		}

		for (Term cp : allDepPreds) {
			currentGoal.addFormula(new SequentFormula(cp), true, false);
//			currentGoal.addFormula(new SequentFormula(cp), false, false);
		}
//		System.out.println("Modified Goal: " + currentGoal);
		return currentGoal;
	}

	void getLow(Sequent seq) {
		for (SequentFormula sf : seq.succedent()) {
			Term formula = sf.formula();
			if (formula.op() instanceof UpdateApplication) {
				Term update = UpdateApplication.getUpdate(formula);
				if (update.op() instanceof ElementaryUpdate) {
					this.low = update.sub(0);
					break;
				}
			}
		}
	}

	void getIndexAndHigh(Sequent seq) {
		Expression high = null, index = null;
		for (final SequentFormula sf : seq.succedent()) {
			final Term formula = skipUpdates(sf.formula());
			if (formula.op() == Modality.DIA) {
				ProgramElement pe = formula.javaBlock().program();
				Statement activePE;
				if (pe instanceof ProgramPrefix) {
					activePE = (Statement) ((ProgramPrefix) pe).getLastPrefixElement().getFirstElement();
				} else {
					activePE = (Statement) pe.getFirstElement();
				}
				if (activePE instanceof While) {
					final Expression expr = ((While) activePE).getGuardExpression();
					if (expr instanceof GreaterOrEquals || expr instanceof GreaterThan) {
						high = ((ComparativeOperator) expr).getExpressionAt(0);
						index = ((ComparativeOperator) expr).getExpressionAt(1);
					} else if (expr instanceof LessOrEquals || expr instanceof LessThan) {
						high = ((ComparativeOperator) expr).getExpressionAt(1);
						index = ((ComparativeOperator) expr).getExpressionAt(0);
					}
				}
				break;
			}
		}
		this.high = expr2term(high);
		this.index = expr2term(index);
	}

	void getLoopGuard(Sequent seq) {
		Term guard = null;
		for (SequentFormula sf : seq.succedent()) {
			final Term formula = skipUpdates(sf.formula());
			if (formula.op() == Modality.DIA) {
				ProgramElement pe = formula.javaBlock().program();
				Statement activePE;
				if (pe instanceof ProgramPrefix) {
					activePE = (Statement) ((ProgramPrefix) pe).getLastPrefixElement().getFirstElement();
				} else {
					activePE = (Statement) pe.getFirstElement();
				}
				if (activePE instanceof While) {
					final Expression expr = ((While) activePE).getGuardExpression();
					final Term left = expr2term(((ComparativeOperator) expr).getExpressionAt(0));
					final Term right = expr2term(((ComparativeOperator) expr).getExpressionAt(1));
					if (expr instanceof GreaterOrEquals) {
						guard = tb.geq(left, right);
					} else if (expr instanceof GreaterThan) {
						guard = tb.gt(left, right);
					} else if (expr instanceof LessOrEquals) {
						guard = tb.leq(left, right);
					} else if (expr instanceof LessThan) {
						guard = tb.lt(left,	right);
					}

				}
				break;
			}
		}
		this.guard = guard;
	}

	private Term expr2term(Expression expr) {
		return this.services.getTypeConverter().convertToLogicElement(expr);
	}

	private Term skipUpdates(Term formula) {
		return formula.op() instanceof UpdateApplication ? UpdateApplication.getTarget(formula) : formula;
	}

	Set<LocationVariable> extractProgramVariable(Statement s) {
		ProgramVariableCollectorWithArrayIndices pvc = new ProgramVariableCollectorWithArrayIndices(s, services);
		pvc.start();
//		System.out.println(pvc.result());
//		System.out.println("my array: " + pvc.array());
//		System.out.println(pvc.index());
		return pvc.result();
	}

	void getLocSet(Sequent seq) {
		// How to find the targeted location set (the array)?
		for (SequentFormula sf : seq.succedent()) {
			Term formula = skipUpdates(sf.formula());
			if (formula.op() == Modality.DIA) {
				Statement activePE = (Statement) formula.javaBlock().program();
				Set<LocationVariable> lvs = extractProgramVariable(activePE);
				findArray(lvs);
			}
		}
	}

	private void findArray(Set<LocationVariable> set) {
		for (LocationVariable v : set) {
			if (v.sort() instanceof ArraySort) {
				// System.out.println(v + " is an array with element sort " + ((ArraySort)
				// v.sort()).elementSort());
				// KeYJavaType kjt = v.getKeYJavaType(services);
				// kjt.getSort(); // logic sort
				// kjt.getJavaType(); // Java type
				// System.out.println(v + " is of KeY sort " + kjt.getSort());
				// System.out.println(v + " is of java type " + kjt.getJavaType());
//				System.out.println("old array: " + v);
				arrays.add(tb.var(v));
			}
		}
	}

	private boolean isComparisonOperator(Term pred) {
		final boolean isComparison =
				pred.op() == intLDT.getLessThan() ||
				pred.op() == intLDT.getGreaterThan() ||
				pred.op() == intLDT.getLessOrEquals() ||
				pred.op() == intLDT.getGreaterOrEquals() ||
				pred.op() == Equality.EQUALS;
		return isComparison;
	}
	
}
