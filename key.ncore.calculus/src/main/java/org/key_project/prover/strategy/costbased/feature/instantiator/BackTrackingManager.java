/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.prover.strategy.costbased.feature.instantiator;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Iterator;

import org.key_project.prover.rules.RuleApp;
import org.key_project.util.collection.ImmutableSLList;

import org.jspecify.annotations.Nullable;


/// Manager for the <code>ChoicePoint</code>s that can occur during the evaluation of a feature
/// term,
/// taking care of the different branches offered by the points, and that is able to systematically
/// explore the resulting search space and enumerate all resulting rule applications.
/// <code>ChoicePoint</code>s have to register themselves (using method
/// <code>passChoicePoint</code>)
/// each time they are invoked during evaluation of the feature term, and are asked by the manager
/// for their branches. The manager simulates a backtracking behaviour by repeated evaluation of the
/// feature term.
public final class BackTrackingManager {

    /// The original rule application in question, i.e., the application without the changes that
    /// can
    /// possibly be applied by <code>ChoicePoint</code>s
    private @Nullable RuleApp initialApp = null;

    /// Stack of <code>Iterator<CPBranch></code>: the branches of <code>ChoicePoint</code>s that
    /// have
    /// not yet been taken, the branches of later points being further up in the stack
    private final ArrayDeque<Iterator<CPBranch>> choices = new ArrayDeque<>();

    /// List of <code>CPBranch</code>: the branches that are taken in the current evaluation run
    private final ArrayList<@Nullable CPBranch> chosenBranches = new ArrayList<>();

    /// The position within <code>choices</code> during the current evaluation run (the number of
    /// <code>ChoicePoint</code>s that occured so far during the current evaluation)
    private int position = 0;

    /// Method that has to be invoked by each feature that represents a choice point, each time the
    /// feature is invoked during evaluation of the feature term
    ///
    /// @param cp the <code>ChoicePoint</code> in question (which does not have to be the same
    /// object
    /// as the feature, and which does not have to be the same object over different
    /// evaluations of the feature term)
    /// @param ticket a unique object (as unique as possible) that has to be provided by the feature
    /// in order to ensure that the same sequence of choice points occurs during the next
    /// evaluation run (after backtracking). The <code>ticket</code> must not change between
    /// two evaluation runs of the feature term
    public void passChoicePoint(ChoicePoint cp, Object ticket) {
        assert initialApp != null;
        assertValidTicket(ticket);
        assert chosenBranches.size() == choices.size();

        if (position == choices.size()) {
            // phase where we have to ask the choice-points for possibilities
            addChoicePoint(cp);
        } else {
            assert choices.size() > position;
            // phase where we have to "replay" choices that have already
            // been made
            final CPBranch branch = chosenBranches.get(position);
            assert branch != null : "@AssumeAssertion(nullness): Branch not found";
            branch.choose();
        }

        ++position;

    }

    /// Method that has to be called before a sequence of evaluation runs of a feature term.
    ///
    /// @param initialApp the original rule application in question
    public void setup(@Nullable RuleApp initialApp) {
        this.initialApp = initialApp;
        choices.clear();
        chosenBranches.clear();
        tickets.clear();
        position = 0;
    }

    /// In the end of an evaluation run of a feature term, this method has to be called for checking
    /// whether it is possible to backtrack and whether a further evaluation run is necessary
    ///
    /// @return <code>true</code> iff there are paths left to explore, i.e., if evaluation should
    /// run
    /// a further time
    public boolean backtrack() {
        position = 0;

        while (!choices.isEmpty()) {
            final Iterator<CPBranch> chs = choices.pop();
            chosenBranches.removeLast();

            if (chs.hasNext()) {
                pushChoices(chs, chs.next());
                return true;
            }

            tickets.removeLast();
        }

        // make sure that no further choicepoints occur until <code>setup</code>
        // is invoked the next time
        setup(null);

        return false;
    }

    /// @return the resulting rule application when all choice points have applied their
    /// modifications
    public @Nullable RuleApp getResultingapp() {
        return getOldRuleApp();
    }

    private void pushChoices(Iterator<CPBranch> remainingChoices, @Nullable CPBranch chosen) {
        choices.push(remainingChoices);
        chosenBranches.add(chosen);
    }

    private void addChoicePoint(ChoicePoint cp) {
        final RuleApp oldApp = getOldRuleApp();
        if (oldApp == null) {
            // This means that an earlier <code>ChoicePoint</code> did not have
            // any branches. It is necessary to backtrack and to choose a
            // different branch for one of the <code>ChoicePoint</code>s before
            // the failing <code>ChoicePoint</code>, but first we have to finish
            // the current evaluation run of the feature term
            cancelChoicePoint();
            return;
        }

        final Iterator<CPBranch> chs = cp.getBranches(oldApp);
        if (!chs.hasNext()) {
            // This <code>ChoicePoint</code> does not have any branches
            cancelChoicePoint();
            return;
        }

        final CPBranch chosen = chs.next();
        pushChoices(chs, chosen);
        chosen.choose();
    }

    private void cancelChoicePoint() {
        pushChoices(ImmutableSLList.<CPBranch>nil().iterator(), null);
    }


    /// List of <code>Object</code>: each <code>ChoicePoint</code> has to install a ticket, which is
    /// used as a sanity check when the evaluation of a feature term is repeated. This is a simple
    /// runtime measure for ensuring that the feature evaluation is deterministic
    private final ArrayList<Object> tickets = new ArrayList<>();

    private void assertValidTicket(Object ticket) {
        if (tickets.size() > position) {
            assert tickets.get(position) == ticket;
        } else {
            assert tickets.size() == position;
            tickets.add(ticket);
        }
    }

    private @Nullable RuleApp getOldRuleApp() {
        if (chosenBranches.isEmpty()) {
            return initialApp;
        }
        final CPBranch branch = chosenBranches.get(position - 1);
        if (branch == null) {
            return null;
        }
        return branch.getRuleAppForBranch();
    }

}
