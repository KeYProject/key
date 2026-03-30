/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.isabelletranslation.automation;

import java.util.ArrayList;
import java.util.List;

import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.AbstractExternalSolverRuleApp;

import org.key_project.logic.PosInTerm;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.sequent.Sequent;
import org.key_project.prover.sequent.SequentFormula;
import org.key_project.util.collection.ImmutableList;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

@NullMarked
public class IsabelleRuleApp extends AbstractExternalSolverRuleApp<IsabelleRule> {

    protected IsabelleRuleApp(IsabelleRule rule, @Nullable PosInOccurrence pio,
            String successfulSolverName,
            String successfulTactic) {
        this(rule, pio, null, successfulSolverName,
            "Isabelle " + successfulSolverName + ": " + successfulTactic);
    }

    protected IsabelleRuleApp(IsabelleRule rule, @Nullable PosInOccurrence pio,
            ImmutableList<PosInOccurrence> ifInsts, String successfulSolverName) {
        this(rule, pio, ifInsts, successfulSolverName, "Isabelle: " + successfulSolverName);
    }

    private IsabelleRuleApp(IsabelleRule rule, @Nullable PosInOccurrence pio,
            ImmutableList<PosInOccurrence> ifInsts, String successfulSolverName, String title) {
        super(rule, pio, ifInsts, successfulSolverName, title);
    }

    @Override
    public IsabelleRuleApp setTitle(String title) {
        return new IsabelleRuleApp(IsabelleRule.INSTANCE, pio, ifInsts, successfulSolverName,
            title);
    }

    @Override
    public IsabelleRuleApp replacePos(PosInOccurrence newPos) {
        return new IsabelleRuleApp(IsabelleRule.INSTANCE, newPos, successfulSolverName, title);
    }

    @Override
    public IsabelleRuleApp tryToInstantiate(Goal goal) {
        IsabelleRuleApp app = IsabelleRule.INSTANCE.createApp(pio, goal.proof().getServices());
        Sequent seq = goal.sequent();
        List<PosInOccurrence> ifInsts = new ArrayList<>();
        for (SequentFormula ante : seq.antecedent()) {
            ifInsts.add(new PosInOccurrence(ante, PosInTerm.getTopLevel(), true));
        }
        for (SequentFormula succ : seq.succedent()) {
            ifInsts.add(new PosInOccurrence(succ, PosInTerm.getTopLevel(), false));
        }
        return app.setAssumesInsts(ImmutableList.fromList(ifInsts));
    }

    @Override
    public IsabelleRuleApp setAssumesInsts(ImmutableList<PosInOccurrence> ifInsts) {
        setMutable(ifInsts);
        return this;
    }

    @Override
    public IsabelleRule rule() {
        return IsabelleRule.INSTANCE;
    }

}
