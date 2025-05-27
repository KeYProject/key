/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.rule.executor.rustydl;

import org.key_project.logic.IntIterator;
import org.key_project.logic.Term;
import org.key_project.logic.op.QuantifiableVariable;
import org.key_project.logic.sort.Sort;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.sequent.Sequent;
import org.key_project.prover.sequent.SequentChangeInfo;
import org.key_project.prover.sequent.SequentFormula;
import org.key_project.rusty.Services;
import org.key_project.rusty.proof.Goal;
import org.key_project.rusty.rule.MatchConditions;
import org.key_project.rusty.rule.RuleApp;
import org.key_project.rusty.rule.Taclet;
import org.key_project.rusty.rule.tacletbuilder.RewriteTacletGoalTemplate;
import org.key_project.rusty.rule.tacletbuilder.TacletGoalTemplate;
import org.key_project.util.collection.ImmutableArray;

public class RewriteTacletExecutor
        extends FindTacletExecutor {

    public RewriteTacletExecutor(Taclet taclet) {
        super(taclet);
    }

    /**
     * adds the sequent of the add part of the Taclet to the goal sequent
     *
     * @param add the Sequent to be added
     * @param currentSequent the Sequent which is the current (intermediate) result of applying the
     *        taclet
     * @param posOfFind describes the application position of the find expression in the original
     *        sequent
     * @param whereToAdd the PosInOccurrence describes the place where to add the semisequent
     * @param matchCond the MatchConditions with all required instantiations
     * @param goal the Goal the taclet is applied to
     * @param ruleApp the rule application to apply
     * @param services the Services encapsulating all Rust information
     */
    @Override
    protected void applyAdd(Sequent add,
            SequentChangeInfo currentSequent, PosInOccurrence whereToAdd, PosInOccurrence posOfFind,
            MatchConditions matchCond, Goal goal, RuleApp ruleApp, Services services) {
        if (posOfFind.isInAntec()) {
            addToAntec(add.antecedent(),
                currentSequent,
                whereToAdd, posOfFind, matchCond, goal, ruleApp, services);
            addToSucc(add.succedent(),
                currentSequent, null,
                posOfFind, matchCond, goal, ruleApp, services);
        } else {
            addToAntec(add.antecedent(),
                currentSequent, null,
                posOfFind, matchCond, goal, ruleApp, services);
            addToSucc(add.succedent(),
                currentSequent, whereToAdd,
                posOfFind, matchCond, goal, ruleApp, services);
        }
    }

    @Override
    protected void applyReplacewith(TacletGoalTemplate gt, SequentChangeInfo currentSequent,
            PosInOccurrence posOfFind, MatchConditions matchCond, Goal goal, RuleApp ruleApp,
            Services services) {
        if (gt instanceof RewriteTacletGoalTemplate rwtgt) {
            final org.key_project.prover.sequent.SequentFormula cf = applyReplacewithHelper(goal,
                rwtgt, posOfFind, services, matchCond, ruleApp);
            currentSequent.combine(currentSequent.sequent().changeFormula(cf, posOfFind));
        } else {
            // Then there was no replacewith...
            // This is strange in a RewriteTaclet, but who knows...
            // However, term label refactorings have to be performed.
            // TODO: labels?
        }
    }

    private org.key_project.prover.sequent.SequentFormula applyReplacewithHelper(Goal goal,
            RewriteTacletGoalTemplate gt, PosInOccurrence posOfFind, Services services,
            MatchConditions matchCond, RuleApp ruleApp) {
        final Term term = posOfFind.sequentFormula().formula();
        final IntIterator it = posOfFind.posInTerm().iterator();
        final Term rwTemplate = gt.replaceWith();

        Term formula = replace(term, rwTemplate,
            posOfFind, it, matchCond, term.sort(), goal, services, ruleApp);
        if (term == formula) {
            return posOfFind.sequentFormula();
        } else {
            return new SequentFormula(formula);
        }
    }

    /**
     * does the work for applyReplacewith (wraps recursion)
     */
    private Term replace(Term term, Term with, PosInOccurrence posOfFind, IntIterator it,
            MatchConditions mc, Sort maxSort, Goal goal, Services services, RuleApp ruleApp) {
        if (it.hasNext()) {
            final int indexOfNextSubTerm = it.next();

            final Term[] subs = new Term[term.arity()];
            term.subs().arraycopy(0, subs, 0, term.arity());

            final Sort newMaxSort = maxSort; // TODO? TermHelper.getMaxSort(term,
                                             // indexOfNextSubTerm);
            subs[indexOfNextSubTerm] = replace(term.sub(indexOfNextSubTerm), with, posOfFind, it,
                mc, newMaxSort, goal, services, ruleApp);

            return services.getTermFactory().createTerm(term.op(), subs,
                (ImmutableArray<QuantifiableVariable>) term.boundVars());
        }

        with = syntacticalReplace(with, posOfFind, mc, goal, ruleApp, services);

        /*
         * if (!with.sort().extendsTrans(maxSort)) {
         * with = services.getTermBuilder().cast(maxSort, with);
         * }
         */

        return with;
    }
}
