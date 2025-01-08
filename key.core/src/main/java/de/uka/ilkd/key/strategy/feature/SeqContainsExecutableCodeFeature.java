/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.feature;

import java.util.Iterator;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.strategy.termfeature.BinaryTermFeature;
import de.uka.ilkd.key.strategy.termfeature.ContainsExecutableCodeTermFeature;
import de.uka.ilkd.key.strategy.termfeature.TermFeature;

import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.sequent.SequentFormula;

public class SeqContainsExecutableCodeFeature extends BinaryFeature {

    private final TermFeature tf;

    private SeqContainsExecutableCodeFeature(boolean considerQueries) {
        if (considerQueries) {
            tf = ContainsExecutableCodeTermFeature.PROGRAMS_OR_QUERIES;
        } else {
            tf = ContainsExecutableCodeTermFeature.PROGRAMS;
        }
    }

    public final static Feature PROGRAMS = new SeqContainsExecutableCodeFeature(false);
    public final static Feature PROGRAMS_OR_QUERIES = new SeqContainsExecutableCodeFeature(true);

    protected boolean filter(RuleApp app, PosInOccurrence pos, Goal goal, MutableState mState) {
        return containsExec(goal.sequent().succedent().iterator(), mState,
            goal.proof().getServices())
                || containsExec(goal.sequent().antecedent().iterator(), mState,
                    goal.proof().getServices());
    }

    private boolean containsExec(Iterator<SequentFormula> it, MutableState mState,
            Services services) {
        while (it.hasNext()) {
            if (tf.compute(it.next().formula(), mState, services)
                    .equals(BinaryTermFeature.ZERO_COST)) {
                return true;
            }
        }
        return false;
    }
}
