package de.uka.ilkd.key.loopinvgen;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.util.Pair;
import org.key_project.util.collection.ImmutableList;

import java.util.Set;

public class LIGNewInnerMltpArr extends AbstractLoopInvariantGenerator {
    Set<Term> allDepPreds;
    Set<Term> allCompPreds;
    Term arrOuter;
    Term arrInner;
    Term indexOuter;
    Term indexInner;

    public LIGNewInnerMltpArr(Sequent sequent, Services services, Set<Term> innerDepPreds, Set<Term> innerCompPreds, Term arrOuter, Term arrInner, Term indexOuter, Term indexInner) {
        super(sequent, services);
        this.allDepPreds = innerDepPreds;
        this.allCompPreds = innerCompPreds;
        this.arrOuter = arrOuter;
        this.arrInner = arrInner;
        this.indexOuter = indexOuter;
        this.indexInner = indexInner;
    }

    @Override
    public LoopInvariantGenerationResult generate() {

        ImmutableList<Goal> goalsAfterShift;
        Goal currentGoal;
        int itrNumber = -1;
        Pair<Set<Term>, Set<Term>> refinedPreds;

        do {
            itrNumber++;
            System.out.println("Inner Iteration Number: " + itrNumber);

            oldDepPreds.clear();
            oldCompPreds.clear();

            oldDepPreds.addAll(allDepPreds);
            oldCompPreds.addAll(allCompPreds);

            ImmutableList<Goal> goalsAfterUnwind = ruleApp.applyUnwindRule(services.getProof().openGoals());
//			System.out.println("Goals After Unwind:" + goalsAfterUnwind);

            goalsAfterShift = ruleApp.applyShiftUpdateRule(goalsAfterUnwind);
            System.out.println("Goals After Shift:" + goalsAfterShift);

            currentGoal = ruleApp.findLoopUnwindTacletGoal(goalsAfterShift);

//			PredicateRefiner pr = new LoopIndexAndDependencyPredicateRefiner(currentGoal.sequent(), allDepPreds, allCompPreds,
//					index, itrNumber, services);
            NestedLoopIndexAndDependencyPredicateRefiner pr = new NestedLoopIndexAndDependencyPredicateRefiner(currentGoal.sequent(), allDepPreds, allCompPreds,
                    arrOuter, arrInner, indexOuter, indexInner, itrNumber, services);
            refinedPreds = pr.refine();
            allDepPreds = refinedPreds.first;
            System.out.println("all dep preds: " + allDepPreds);
            allCompPreds = refinedPreds.second;

            for (Goal g : goalsAfterShift) {
                if (g != null)
                    abstractGoal(g, allCompPreds, allDepPreds);
            }
        } while ((!allCompPreds.equals(oldCompPreds) || !allDepPreds.equals(oldDepPreds)) || itrNumber < 2);

        allDepPreds.addAll(allCompPreds);

//		final PredicateSetCompressor compressor =
//				new PredicateSetCompressor(allDepPreds, currentGoal.sequent(), false, services);
//		allDepPreds = compressor.compress();
        final LoopInvariantGenerationResult loopInv = new LoopInvariantGenerationResult(allDepPreds, itrNumber, services);
        System.out.println("Inner loop inv is: " + loopInv);
        return loopInv;
    }
}
