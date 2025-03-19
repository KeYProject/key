/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.loopinvgen;

import java.util.Set;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.loopinvgen.analyzer.WhileStatementAnalyzer;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.io.ProofSaver;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.Pair;

public class LIGNew extends AbstractLoopInvariantGenerator {

    Term outerIndex;
    final boolean relaxed;

    public LIGNew(Sequent sequent, Services services, ProgramVariable index, int nrArrays) {
        super(sequent, services, services.getTypeConverter().convertToLogicElement(index),
            nrArrays);
        relaxed = false;
    }

    public LIGNew(Sequent sequent, Services services, ProgramVariable index, int nrArrays,
            boolean relaxed) {
        super(sequent, services, services.getTypeConverter().convertToLogicElement(index),
            nrArrays);
        this.relaxed = relaxed;
    }

    public LIGNew(Sequent sequent, Services services, boolean relaxed) {
        super(sequent, services);
        this.relaxed = relaxed;
    }

    /*
     * public LIGNew(Sequent sequent, Services services, Term outerIndex) {
     * super(sequent, services);
     * this.outerIndex = outerIndex;
     * }
     */

    @Override
    public LoopInvariantGenerationResult generate() {

        System.out.println(ProofSaver.printAnything(
            WhileStatementAnalyzer.determineInitialIndex(seq, index, services), services));
        // getLow(seq);
        setInitialIndexValue();
        getHigh(seq);
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

        ImmutableList<Goal> goalsAfterShift =
            ruleApp.applyShiftUpdateRule(services.getProof().openGoals());
        // System.out.println("SHIFTED");
        // System.out.println("number of goals after shift number -1: " + goalsAfterShift.size());//
        // It is always one
        // System.out.println(
        // "Goals after shift -1: " + ProofSaver.printAnything(goalsAfterShift.head().sequent(),
        // services));

        Goal currentGoal = goalsAfterShift.head();// Number of goals after shift does not change

        // // Initial Predicate Sets for stencil, conditionalWithDifferentEvents:
        // allCompPreds.add(tb.geq(index, tb.sub(low,tb.one())));//
        // allCompPreds.add(tb.leq(index, tb.add(high, tb.one())));//
        // for (Term arr : arrays) {
        // allDepPreds.add(tb.noR(tb.arrayRange(arr, tb.sub(low,tb.one()), high)));
        // allDepPreds.add(tb.noW(tb.arrayRange(arr, tb.sub(low,tb.one()), high)));
        // }

        // Initial Predicate Sets for shiftArrayToLeft, shiftArrayToLeftWithBreak, withoutFunc,
        // withFunc, conditionWithDifferentNumberOfEvent, condition:
        allCompPreds.add(tb.geq(index, low));
        allCompPreds.add(tb.leq(index, tb.add(high, tb.one())));
        initializeAbstractDomain();


        // System.out.println("Initial comp Predicate Set: " + allCompPreds);
        // for (Term term : allPreds) {
        // System.out.println(term);
        // }
        int itrNumber = -1;
        PredicateRefiner pr0 = new LoopIndexAndDependencyPredicateRefiner(currentGoal.sequent(),
            allDepPreds, allCompPreds, outerIndex,
            index, itrNumber, services);
        Pair<Set<Term>, Set<Term>> refinedPreds = pr0.refine();
        // System.out.println(ProofSaver.printAnything(seq, services));
        allDepPreds = refinedPreds.first;
        allCompPreds = refinedPreds.second;

        // for (Goal g : goalsAfterShift) {
        // g = abstractGoal(g);
        // }

        do {
            itrNumber++;
            // System.out.println("Iteration Number: " + itrNumber);

            oldDepPreds.clear();
            oldCompPreds.clear();

            oldDepPreds.addAll(allDepPreds);
            oldCompPreds.addAll(allCompPreds);

            // System.out.println("BEFORE UNWIND");
            // System.out.println(goalsAfterShift);
            // System.out.println("Goals Before Unwind:" + goalsAfterShift);

            ImmutableList<Goal> goalsAfterUnwind;
            if (!relaxed) {
                goalsAfterUnwind = ruleApp.applyUnwindRule(goalsAfterShift);
            } else {
                goalsAfterUnwind = ruleApp.applyLoopScopeUnwindRule(goalsAfterShift);
            }

            goalsAfterShift = ruleApp.applyShiftUpdateRule(goalsAfterUnwind);

            if (!relaxed) {
                currentGoal = ruleApp.findLoopUnwindTacletGoal(goalsAfterShift);
            } else {
                currentGoal = ruleApp.findLoopScopeLoopUnwindTacletGoal(goalsAfterShift);
            }

            // System.out.println("Current Goal: " + currentGoal);
            // currentIndexFormula = currentIndexEq(currentGoal.sequent(), index);
            // System.out.println("Before refinement: " + currentGoal.sequent());

            PredicateRefiner pr = new LoopIndexAndDependencyPredicateRefiner(currentGoal.sequent(),
                allDepPreds, allCompPreds, outerIndex,
                index, itrNumber, services);
            refinedPreds = pr.refine();
            allDepPreds = refinedPreds.first;
            allCompPreds = refinedPreds.second;

            // currentGoal = abstractGoal(currentGoal);
            for (Goal g : goalsAfterShift) {
                abstractGoal(g, allCompPreds, allDepPreds);
            }
            // System.out.println("Dep Preds: " + allDepPreds);
        } while ((!allCompPreds.equals(oldCompPreds) || !allDepPreds.equals(oldDepPreds))
                || itrNumber < 2);

        allDepPreds.addAll(allCompPreds);

        final PredicateSetCompressor compressor =
            new PredicateSetCompressor(allDepPreds, currentGoal.sequent(), false, services);
        allDepPreds = compressor.compress();
        LoopInvariantGenerationResult result =
            new LoopInvariantGenerationResult(allDepPreds, itrNumber, services);
        System.out.println("Loop Invariant is: " + result);
        return result;
    }

    protected void setInitialIndexValue() {
        this.low = WhileStatementAnalyzer.determineInitialIndex(seq, index, services);
    }

    protected void initializeAbstractDomain() {
        if (!relaxed) {
            for (Term arr : arrays) {
                allDepPreds.add(tb.noR(tb.arrayRange(arr, low, high)));
                allDepPreds.add(tb.noW(tb.arrayRange(arr, low, high)));
            }
        } else {
            for (Term arr : arrays) {
                allDepPreds.add(tb.relaxedNoR(tb.arrayRange(arr, low, high)));
                allDepPreds.add(tb.relaxedNoW(tb.arrayRange(arr, low, high)));
            }
        }

    }

}
