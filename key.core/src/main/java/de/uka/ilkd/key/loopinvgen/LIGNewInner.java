/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.loopinvgen;

import java.util.Set;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.Goal;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.Pair;

public class LIGNewInner extends AbstractLoopInvariantGenerator {
    Set<Term> allDepPreds;
    Set<Term> allCompPreds;
    Term outerIndex;

    public LIGNewInner(Sequent sequent, Services services, Set<Term> innerDepPreds,
            Set<Term> innerCompPreds) {
        super(sequent, services);
        this.allDepPreds = innerDepPreds;
        this.allCompPreds = innerCompPreds;
    }

    public LIGNewInner(Sequent sequent, Services services, Set<Term> innerDepPreds,
            Set<Term> innerCompPreds, Term outerIndex, Term innerIndex, int nrArrays) {
        super(sequent, services, innerIndex, nrArrays);
        this.allDepPreds = innerDepPreds;
        this.allCompPreds = innerCompPreds;
        this.outerIndex = outerIndex;
        this.index = innerIndex;
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

            ImmutableList<Goal> goalsAfterUnwind =
                ruleApp.applyUnwindRule(services.getProof().openGoals());
            // System.out.println("Goals After Unwind:" + goalsAfterUnwind);

            goalsAfterShift = ruleApp.applyShiftUpdateRule(goalsAfterUnwind);
            // System.out.println("Goals After Shift:" + goalsAfterShift);

            currentGoal = ruleApp.findLoopUnwindTacletGoal(goalsAfterShift);

            PredicateRefiner pr = new LoopIndexAndDependencyPredicateRefiner(currentGoal.sequent(),
                allDepPreds, allCompPreds, outerIndex,
                index, itrNumber, services);
            refinedPreds = pr.refine();
            allDepPreds = refinedPreds.first;
            allCompPreds = refinedPreds.second;


            // HashMap<Term, List<Term>> locSets2predicates = new HashMap<>();
            // for (Term pred: allDepPreds) {
            // List<Term> list;
            // if (locSets2predicates.containsKey(pred.sub(0))) {
            // list = locSets2predicates.get(pred.sub(0));
            // } else {
            // list = new LinkedList<Term>();
            // }
            // list.add(pred);
            // locSets2predicates.put(pred.sub(0), list);
            // }
            //
            // var it = locSets2predicates.entrySet();
            // System.out.println("====>>>>");
            // for(var entry : it) {
            // System.out.println(entry.getKey() + ":" + entry.getValue().size() + ":" +
            // entry.getValue());
            // }


            for (Goal g : goalsAfterShift) {
                if (g != null)
                    abstractGoal(g, allCompPreds, allDepPreds);
            }
        } while ((!allCompPreds.equals(oldCompPreds) || !allDepPreds.equals(oldDepPreds))
                || itrNumber < 2);

        allDepPreds.addAll(allCompPreds);

        final PredicateSetCompressor compressor =
            new PredicateSetCompressor(allDepPreds, currentGoal.sequent(), false, services);
        allDepPreds = compressor.compress();
        System.out.println("Compressd!");


        final LoopInvariantGenerationResult loopInv =
            new LoopInvariantGenerationResult(allDepPreds, itrNumber, services);
        System.out.println("Inner loop inv is: " + loopInv);
        return loopInv;
    }
}
