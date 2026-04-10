/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.smt;

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
 * @author Alexander Weigl
 * @version 1 (8/3/25)
 */
@NullMarked
public class SMTRule implements ExternalSolverRule {
    public static final Name name = new Name("SMTRule");
    public static final SMTRule INSTANCE = new SMTRule();

    @Override
    public SMTRuleApp createApp(String successfulSolverName) {
        return new SMTRuleApp(this, null, successfulSolverName);
    }

    /**
     * Create a new rule application with the given solver name and unsat core.
     *
     * @param successfulSolverName solver that produced this result
     * @param unsatCore formulas required to prove the result
     * @return rule application instance
     */
    @Override
    public <T extends ExternalSolverRule> AbstractExternalSolverRuleApp<T> createApp(
            String successfulSolverName, ImmutableList<PosInOccurrence> unsatCore) {
        // weigl strange
        AbstractExternalSolverRuleApp<?> x =
            new SMTRuleApp(this, null, unsatCore, successfulSolverName);
        return (AbstractExternalSolverRuleApp<T>) x;
    }


    @Override
    public SMTRuleApp createApp(PosInOccurrence pos, TermServices services) {
        return new SMTRuleApp(this, null, "");
    }


    @Override
    public boolean isApplicable(Goal goal, PosInOccurrence pio) {
        return false;
    }


    /**
     * Create a new goal (to be closed in
     * {@link Goal#apply(RuleApp)} directly afterwards)
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
    public String displayName() {
        return "SMT";
    }

    @Override
    public String toString() {
        return displayName();
    }

    @Override
    public Name name() {
        return name;
    }
}
