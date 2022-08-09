package de.uka.ilkd.key.loopinvgen;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.util.Pair;
import org.key_project.util.collection.ImmutableList;

import java.util.Set;

public class LIGNewInner extends AbstractLoopInvariantGenerator {
	Set<Term> allDepPreds;
	Set<Term> allCompPreds;
	public LIGNewInner(Sequent sequent, Services services, Set<Term> innerDepPreds, Set<Term> innerCompPreds) {
		super(sequent, services);
		this.allDepPreds = innerDepPreds;
		this.allCompPreds = innerCompPreds;
	}

	@Override
	public LoopInvariantGenerationResult generate() {

		ImmutableList<Goal> goalsAfterShift ;//= ruleApp.applyShiftUpdateRule(services.getProof().openGoals());
//		System.out.println("SHIFTED");
//		System.out.println("number of goals after shift number -1: " + goalsAfterShift.size());// It is always one
//		System.out.println(
//				"Goals after shift -1: " + ProofSaver.printAnything(goalsAfterShift.head().sequent(), services));

		Goal currentGoal;// = goalsAfterShift.head();// Number of goals after shift does not change

		int itrNumber = -1;
//		PredicateRefiner pr0 = new LoopIndexAndDependencyPredicateRefiner(currentGoal.sequent(), allDepPreds, allCompPreds,
//				index, itrNumber, services);
		Pair<Set<Term>, Set<Term>> refinedPreds;// = pr0.refine();
//		System.out.println(ProofSaver.printAnything(seq, services));
//		allDepPreds = refinedPreds.first;
//		allCompPreds = refinedPreds.second;
//
//		for (Goal g : goalsAfterShift) {
//			if(g!=null){
//				abstractGoal(g,allCompPreds,allDepPreds);
//			}
//		}

		do {
			itrNumber++;
//			System.out.println("Inner Iteration Number: " + itrNumber);

			oldDepPreds.clear();
			oldCompPreds.clear();

			oldDepPreds.addAll(allDepPreds);
			oldCompPreds.addAll(allCompPreds);

//			System.out.println("BEFORE UNWIND");
//			System.out.println(goalsAfterShift);
//			System.out.println("Goals Before Unwind:" + goalsAfterShift);

			ImmutableList<Goal> goalsAfterUnwind = ruleApp.applyUnwindRule(services.getProof().openGoals());
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

			PredicateRefiner pr = new LoopIndexAndDependencyPredicateRefiner(currentGoal.sequent(), allDepPreds, allCompPreds,
					index, itrNumber, services);
			refinedPreds = pr.refine();
			allDepPreds = refinedPreds.first;
			allCompPreds = refinedPreds.second;

//			currentGoal = abstractGoal(currentGoal);
			for (Goal g : goalsAfterShift) {
				if(g!=null)
					abstractGoal(g, allCompPreds,allDepPreds);
			}
//			System.out.println("Dep Preds: " + allDepPreds);
		} while ((!allCompPreds.equals(oldCompPreds) || !allDepPreds.equals(oldDepPreds)) || itrNumber < 2);

		allDepPreds.addAll(allCompPreds);

		final PredicateSetCompressor compressor =
				new PredicateSetCompressor(allDepPreds, currentGoal.sequent(), false, services);
		allDepPreds = compressor.compress();
		System.out.println("Inner loop inv is: ");
		LoopInvariantGenerationResult ligr = new LoopInvariantGenerationResult(allDepPreds, itrNumber);
		ligr.toString();
		return ligr;
	}

}
