/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.isabelletranslation.automation;

import java.util.ArrayList;
import java.util.List;

import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.AbstractExternalSolverRuleApp;

import org.key_project.logic.Name;
import org.key_project.logic.PosInTerm;
import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.sequent.Sequent;
import org.key_project.prover.sequent.SequentFormula;
import org.key_project.util.collection.ImmutableList;

import org.jspecify.annotations.NonNull;

public class IsabelleRuleApp extends AbstractExternalSolverRuleApp {
    public static final IsabelleRule RULE = new IsabelleRule();

    protected IsabelleRuleApp(IsabelleRule rule, PosInOccurrence pio, String successfulSolverName,
            String successfulTactic) {
        this(rule, pio, null, successfulSolverName,
            "Isabelle " + successfulSolverName + ": " + successfulTactic);
    }

    protected IsabelleRuleApp(IsabelleRule rule, PosInOccurrence pio,
            ImmutableList<PosInOccurrence> ifInsts, String successfulSolverName) {
        this(rule, pio, ifInsts, successfulSolverName, "Isabelle: " + successfulSolverName);
    }

    private IsabelleRuleApp(IsabelleRule rule, PosInOccurrence pio,
            ImmutableList<PosInOccurrence> ifInsts, String successfulSolverName, String title) {
        super(rule, pio, ifInsts, successfulSolverName, title);
    }

    @Override
    public IsabelleRuleApp setTitle(String title) {
        return new IsabelleRuleApp(RULE, pio, ifInsts, successfulSolverName, title);
    }

    @Override
    public IsabelleRuleApp replacePos(PosInOccurrence newPos) {
        return new IsabelleRuleApp(RULE, newPos, successfulSolverName, title);
    }

    @Override
    public IsabelleRuleApp tryToInstantiate(Goal goal) {
        IsabelleRuleApp app = RULE.createApp(pio, goal.proof().getServices());
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
        return RULE;
    }

    public static class IsabelleRule implements ExternalSolverRule {
        Name name = new Name("IsabelleRule");

        public IsabelleRuleApp createApp(String successfulSolverName,
                String successfulTactic) {
            return new IsabelleRuleApp(this, null, successfulSolverName, successfulTactic);
        }

        @Override
        public IsabelleRuleApp createApp(String successfulSolverName) {
            return new IsabelleRuleApp(this, null, successfulSolverName, "");
        }

        @Override
        public IsabelleRuleApp createApp(String successfulSolverName,
                ImmutableList<PosInOccurrence> unsatCore) {
            return new IsabelleRuleApp(this, null, unsatCore, successfulSolverName);
        }

        @Override
        public IsabelleRuleApp createApp(PosInOccurrence pos, TermServices services) {
            return new IsabelleRuleApp(this, null, "", "");
        }

        /**
         * Create a new goal (to be closed in {@link Goal#apply(RuleApp)} directly afterwards)
         * with the same sequent as the given one.
         *
         * @param goal the Goal on which to apply <tt>ruleApp</tt>
         * @param ruleApp the rule application to be executed
         * @return a list with an identical goal as the given <tt>goal</tt>
         */
        @Override
        @NonNull
        public ImmutableList<Goal> apply(Goal goal, RuleApp ruleApp) {
            if (goal.proof().getInitConfig().getJustifInfo().getJustification(RULE) == null) {
                goal.proof().getInitConfig().registerRule(RULE, () -> false);
            }
            return goal.split(1);
        }

        @Override
        public String toString() {
            return displayName();
        }

        @Override
        public String displayName() {
            return "Isabelle";
        }

        @Override
        public Name name() {
            return name;
        }
    }
}
