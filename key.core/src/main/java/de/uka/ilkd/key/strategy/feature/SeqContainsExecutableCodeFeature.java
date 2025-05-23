/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.feature;

import java.util.Iterator;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.strategy.termfeature.ContainsExecutableCodeTermFeature;

import org.key_project.prover.proof.ProofGoal;
import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.sequent.SequentFormula;
import org.key_project.prover.strategy.costbased.MutableState;
import org.key_project.prover.strategy.costbased.feature.BinaryFeature;
import org.key_project.prover.strategy.costbased.feature.Feature;
import org.key_project.prover.strategy.costbased.termfeature.BinaryTermFeature;
import org.key_project.prover.strategy.costbased.termfeature.TermFeature;

import org.jspecify.annotations.NonNull;

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
    public final static Feature PROGRAMS_OR_QUERIES =
        new SeqContainsExecutableCodeFeature(true);

    @Override
    protected <Goal extends ProofGoal<@NonNull Goal>> boolean filter(RuleApp app,
            PosInOccurrence pos, Goal goal, MutableState mState) {
        final Services services = (Services) goal.proof().getServices();
        return containsExec(goal.sequent().succedent().iterator(), mState, services)
                || containsExec(goal.sequent().antecedent().iterator(), mState, services);
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
