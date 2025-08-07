/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.isabelletranslation.automation;

import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.AbstractExternalSolverRuleApp;
import de.uka.ilkd.key.rule.ExternalSolverRule;

import org.key_project.logic.Name;
import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.util.collection.ImmutableList;

import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.NullMarked;

/**
 *
 * @author Alexander Weigl
 * @version 1 (8/7/25)
 */
@NullMarked
public class IsabelleRule implements ExternalSolverRule {
    public static final IsabelleRule INSTANCE = new IsabelleRule();

    public static final Name NAME = new Name("IsabelleRule");

    public IsabelleRuleApp createApp(String successfulSolverName,
            String successfulTactic) {
        return new IsabelleRuleApp(this, null, successfulSolverName, successfulTactic);
    }

    @Override
    public IsabelleRuleApp createApp(String successfulSolverName) {
        return new IsabelleRuleApp(this, null, successfulSolverName, "");
    }

    @Override
    public <T extends ExternalSolverRule> AbstractExternalSolverRuleApp<T> createApp(
            String successfulSolverName, ImmutableList<PosInOccurrence> unsatCore) {
        var app = new IsabelleRuleApp(this, null, unsatCore, successfulSolverName);
        return (AbstractExternalSolverRuleApp<T>) app;
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
        if (goal.proof().getInitConfig().getJustifInfo().getJustification(INSTANCE) == null) {
            goal.proof().getInitConfig().registerRule(INSTANCE, () -> false);
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
        return NAME;
    }
}
