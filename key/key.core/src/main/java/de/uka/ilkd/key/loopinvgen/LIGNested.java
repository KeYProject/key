package de.uka.ilkd.key.loopinvgen;

import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.Statement;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.statement.LoopStatement;
import de.uka.ilkd.key.java.statement.While;
import de.uka.ilkd.key.ldt.DependenciesLDT;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.io.ProofSaver;
import de.uka.ilkd.key.speclang.LoopSpecification;
import de.uka.ilkd.key.util.Pair;
import org.key_project.util.collection.ImmutableList;

import java.util.*;

public class LIGNested  extends AbstractLoopInvariantGenerator {
	private final DependenciesLDT depLDT;
	private final HeapLDT heapLDT;

	public LIGNested(Sequent sequent, Services services) {
		super(sequent, services);
		depLDT = services.getTypeConverter().getDependenciesLDT();
		heapLDT = services.getTypeConverter().getHeapLDT();
	}

	public LoopInvariantGenerationResult generate() {
		initialization();
//		System.out.println("Goals before shift number -1: "+services.getProof().openGoals());
		ImmutableList<Goal> goalsAfterShift = ruleApp.applyShiftUpdateRule(services.getProof().openGoals());
//		System.out.println("number of goals after shift number -1: " + goalsAfterShift.size());// It is always one
//		System.out.println(
//				"Goals after shift -1: " + ProofSaver.printAnything(goalsAfterShift.head().sequent(), services));
		// Number of goals after shift does not change

//		// Initial Predicate Sets for stencil and conditionalWithDifferentEvents: 
//		allCompPreds.add(tb.geq(index, tb.sub(low,tb.one())));//
//		allCompPreds.add(tb.leq(index, tb.add(high, tb.one())));//
//		for (Term arr : arrays) {
//			allDepPreds.add(tb.noR(tb.arrayRange(arr, tb.sub(low,tb.one()), high)));
//			allDepPreds.add(tb.noW(tb.arrayRange(arr, tb.sub(low,tb.one()), high)));
//		}

//		//Initial Predicate Sets for shiftArrayToLeft, shiftArrayToLeftWithBreak, withoutFunc, withFunc, conditionWithDifferentNumberOfEvent, condition:
		outerCompPreds.add(tb.geq(indexOuter, lowOuter));
		outerCompPreds.add(tb.leq(indexOuter, tb.add(highOuter, tb.one())));
		for (Term arr : arrays) {
			outerDepPreds.add(tb.noR(tb.arrayRange(arr, lowOuter, highOuter)));
			outerDepPreds.add(tb.noW(tb.arrayRange(arr, lowOuter, highOuter)));
		}
		innerCompPreds.add(tb.geq(indexInner, lowInner));
		innerCompPreds.add(tb.leq(indexInner, tb.add(highInner, tb.one())));
		for (Term arr : arrays) {
			innerDepPreds.add(tb.noR(tb.arrayRange(arr, lowInner, highInner)));
			innerDepPreds.add(tb.noW(tb.arrayRange(arr, lowInner, highInner)));
		}
//		System.out.println(outerCompPreds.toString());
		int outerItrNumber = -1;
		PredicateRefiner prInner =
				new NestedLoopIndexAndDependencyPredicateRefiner(goalsAfterShift.head().sequent(),
						innerDepPreds, innerCompPreds,
						indexOuter, indexInner, outerItrNumber, services);
		Pair<Set<Term>, Set<Term>> refinedInnerPreds = prInner.refine();
		innerDepPreds = refinedInnerPreds.first;
		innerCompPreds = refinedInnerPreds.second;

		PredicateRefiner prOuter =new NestedLoopIndexAndDependencyPredicateRefiner(goalsAfterShift.head().sequent(),
				outerDepPreds, outerCompPreds,
				indexOuter, indexInner, outerItrNumber, services);
		Pair<Set<Term>, Set<Term>> refinedOuterPreds = prOuter.refine();
		outerDepPreds = refinedOuterPreds.first;
		outerCompPreds = refinedOuterPreds.second;
//		System.out.println("Outer Comp Preds" + outerCompPreds.toString());
		Goal currentGoal = null;
		do {
			outerItrNumber++;
//			**		
			System.out.println("OUTER Iteration Number: " + outerItrNumber);

			oldOuterDepPreds.clear();
			oldOuterCompPreds.clear();

			oldOuterDepPreds.addAll(outerDepPreds);
			oldOuterCompPreds.addAll(outerCompPreds);

			ImmutableList<Goal> goalsAfterUnwind = ruleApp.applyUnwindRule(goalsAfterShift);

			LoopStatement innerLoop = null;
			LoopInvariantGenerationResult innerLI = null;
			boolean nested = false;
			for (Goal g : goalsAfterUnwind) {
				for (final SequentFormula sf : g.sequent().succedent()) {
					final Term formula = tb.goBelowUpdates(sf.formula());
					if (formula.op() == Modality.DIA) {
						ProgramElement pe = formula.javaBlock().program();
						Statement activePE;
						if (pe instanceof ProgramPrefix) {
							activePE = (Statement) ((ProgramPrefix) pe).getLastPrefixElement().getFirstElement();
						} else {
							activePE = (Statement) pe.getFirstElement();
						}
						if (activePE instanceof While) {
//							System.out.println("Nested Loop!");
							nested = true;//Even if the loop is not nested the modality starts with a While. I should find another way to distinguish between nested and normal loops
							innerLoop = (LoopStatement) activePE;
							innerLI = innerLIComputation(g, outerItrNumber, activePE);
						}
						break;
					}
				}
//				System.out.println("Goals after unwind no "+outerItrNumber+" and generationg inner LI: "+ goalsAfterUnwind.head());
				//Take everything after the inner loop and before the outer, e.g. i++ and turn it to update and shift it.
				ImmutableList<Goal> goalsAfterShiftUpdate = ruleApp.applyShiftUpdateRule(goalsAfterUnwind);
//				System.out.println("Goals after unwind, generating Inner LI and shift no "+outerItrNumber +" : "+ goalsAfterShiftUpdate.head());
				if (nested) {
					nested = false;
					LoopSpecification loopSpec = new LoopSpecificationImpl(innerLoop, tb.and(innerLI.getConjuncts()));
					services.getSpecificationRepository().addLoopInvariant(loopSpec);
//					System.out.println("Goals before : " + goalsAfterShiftUpdate.head());
					ImmutableList<Goal> goalsAfterNestedLoopUsecase = ruleApp.applyNestedLoopUsecaseRule(goalsAfterShiftUpdate);
//					System.out.println("Goals after nested: "+ goalsAfterNestedLoopUsecase);
					goalsAfterShift = ruleApp.applyShiftUpdateRule(goalsAfterNestedLoopUsecase);
//					System.out.println("Goals After Everything : "+ goalsAfterShiftUpdate.size()+ "  " + goalsAfterShiftUpdate);
				}
			}
			currentGoal = ruleApp.findLoopUnwindTacletGoal(goalsAfterShift);
			System.out.println("current goal: " + currentGoal);
			PredicateRefiner prOuter1 =
					new NestedLoopIndexAndDependencyPredicateRefiner(currentGoal.sequent(),
							outerDepPreds, outerCompPreds,
							indexOuter, indexInner, outerItrNumber, services);
			Pair<Set<Term>, Set<Term>> refinedOuterPreds1 = prOuter1.refine();
//		System.out.println(ProofSaver.printAnything(seq, services));
			outerDepPreds = refinedOuterPreds1.first;
			outerCompPreds = refinedOuterPreds1.second;


		} while ((!outerCompPreds.equals(oldOuterCompPreds) || !outerDepPreds.equals(oldOuterDepPreds)) || outerItrNumber < 2);

		outerDepPreds.addAll(outerCompPreds);

		PredicateSetCompressor compressor =
				new PredicateSetCompressor(outerDepPreds, currentGoal.sequent(), false, services);
		outerDepPreds = compressor.compress();
		LoopInvariantGenerationResult outLoopInv = new LoopInvariantGenerationResult(outerDepPreds, outerItrNumber);
		System.out.println("Outer loops invariant: " + outLoopInv.toString());
		return outLoopInv;
	}

	private void initialization() {
		getLows(seq);
		getIndexesAndHighs(seq);
		getLocSet(seq);

		for (SequentFormula sf : seq.antecedent()) {
			if (!sf.formula().containsJavaBlockRecursive() && isComparisonOperator(sf.formula())) {
				innerCompPreds.add(sf.formula());
				outerCompPreds.add(sf.formula());
			}
		}
		for (SequentFormula sf : seq.succedent()) {
			if (!sf.formula().containsJavaBlockRecursive() && isComparisonOperator(sf.formula())) {
				innerCompPreds.add(tb.not(sf.formula()));
				outerCompPreds.add(tb.not(sf.formula()));
			}
		}
	}

//	private boolean findDiamond(Term t) {
//		if(t instanceof SequentFormula) {
//			SequentFormula sf = (SequentFormula) t;
//			if (sf.formula().op() == Modality.DIA) {
//				return true;
//			} else if (sf.formula().op() instanceof UpdateApplication) {
//				findDiamond(sf.formula().sub(1));
//			}
//		}
//		return false;
//	}


//	private Term constructW(Sequent seqZero, Term readLocSet, Term writtenLocSet, Term rawLocSet, Term warLocSet){//assuming loop does not creat new objects
//		//readEv, writeEv, readEv
//		Term w = null;
//
//		Term readEv1 = tb.anonEventUpdate(rawLocSet, tb.zTerm(2));
//		Term writeEv = tb.anonEventUpdate(tb.union(rawLocSet, warLocSet), tb.zTerm(1));
//		Term readEv2 = tb.anonEventUpdate(warLocSet, tb.zTerm(0));
//		w = tb.sequential(readEv1, tb.sequential(writeEv,readEv2));
//		return w;
//	}

//	private Term extractWaRLocs(LoopInvariantGenerationResult innerLI, Term intersectRandW) {
//		Term locSet =null;
//
//		for(Term pred: innerLI.getConjuncts()){
//			if (pred.op() == depLDT.getNoWaR()){
//				locSet = pred.sub(0);
//				break;
//			}
//		}
//		System.out.println("noWaR LocSet: "+locSet);
//
//		if(locSet!=null){
//			locSet = tb.intersect(locSet, intersectRandW);
//		}
//		System.out.println("Read and written LocSets but noWaR: " + locSet);
//
//		return locSet;
//	}
//	private Term extractRaWLocs(LoopInvariantGenerationResult innerLI, Term intersectRandW) {
//		Term locSet =null;
//
//		for(Term pred: innerLI.getConjuncts()){
//			if (pred.op().equals(depLDT.getNoRaW())){
//				locSet = pred.sub(0);
//				break;
//			}
//		}
//		System.out.println("noRaW LocSet: "+locSet);
//
//		if(locSet!=null){
//			locSet = tb.intersect(locSet, intersectRandW);
//		}
//		System.out.println("Read and written LocSets but noRaW: " + locSet);
//
//		return locSet;
//	}

//	private Term readLocSets(LoopInvariantGenerationResult innerLI) {//assuming we have only one noR in the LI and it doesn't have \cap or \cup in it
//		Term locSet =null;
//		for(Term pred: innerLI.getConjuncts()){
//			if (pred.op().equals(depLDT.getNoR())){
//				locSet = pred.sub(0);
//				break;
//			}
//		}
//		System.out.println("Unread LocSet: "+locSet);
//
//		Set<Term> arr = getInnerLocSets();
//		Set<Term> ret = new HashSet<>();
//		Term retTerm = null;
//
//		if(locSet!=null){
//			for(Term a:arr){
//				if(locSet.sub(0)==a.sub(0)) {//Same array
//					ret.add(tb.setMinus(a, locSet));
//				}
//			}
//		}
//		retTerm = tb.union(ret);
//		System.out.println("Read LocSets is: "+retTerm);
//
//		return retTerm;
//
//	}

//	private Term writtenLocSets(LoopInvariantGenerationResult innerLI) {//assuming we have only one noW in the LI and it doesn't have \cap or \cup in it
//		Term locSet =null;
//		for(Term pred: innerLI.getConjuncts()){
//			if (pred.op().equals(depLDT.getNoW())){
//				locSet = pred.sub(0);
//				break;
//			}
//		}
//		System.out.println("Unwritten LocSet: "+locSet);
//
//		Set<Term> arr = getInnerLocSets();
//		Set<Term> ret = new HashSet<>();
//		Term retTerm = null;
//		if(locSet!=null){
//			for(Term a:arr){
//				if(locSet.sub(0)==a.sub(0)) {//Same array
//					ret.add(tb.setMinus(a, locSet));
//				}
//			}
//		}
//		retTerm = tb.union(ret);
//		System.out.println("Written LocSets is: "+retTerm);
//
//		return retTerm;
//	}


	private LoopInvariantGenerationResult innerLIComputation(Goal g, int itrNumber, Statement activePE) {
//		System.out.println("Entered innerLIComputation");

		StatementBlock stmtBlck = new StatementBlock(activePE);
		JavaBlock jb = JavaBlock.createJavaBlock(stmtBlck);
		Term newDiamond = tb.dia(jb, tb.tt());
		SequentFormula newSF = new SequentFormula(newDiamond);
		Semisequent newSucc = new Semisequent(newSF);

		Sequent newSeq = Sequent.createSequent(g.sequent().antecedent(),newSucc);
//		System.out.println("New Seq for inner loop:  "+ newSeq);

		LIGNewInner innerLIG = new LIGNewInner(newSeq,services, innerDepPreds, innerCompPreds);
		LoopInvariantGenerationResult loopInvariantGenerationResult = innerLIG.generate();

		return loopInvariantGenerationResult;
	}
}
