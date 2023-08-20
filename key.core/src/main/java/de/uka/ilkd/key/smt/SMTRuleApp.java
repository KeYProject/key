/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.smt;

import java.util.ArrayList;
import java.util.List;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.AbstractBuiltInRuleApp;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.rule.RuleApp;

import org.key_project.util.collection.ImmutableList;

/**
 * The rule application that is used when a goal is closed by means of an external solver. So far it
 * stores the rule that that has been used and a title containing some information for the user.
 */
public class SMTRuleApp extends AbstractBuiltInRuleApp {

    public static final SMTRule RULE = new SMTRule();
    private final String title;
    private final String successfulSolverName;

    /**
     * Create a new rule app without ifInsts (will be null).
     *
     * @param rule the SMTRule to apply
     * @param pio the pos in term to apply the rule on
     * @param successfulSolverName the name of the solver that was able to close find the proof
     */
    SMTRuleApp(SMTRule rule, PosInOccurrence pio, String successfulSolverName) {
        this(rule, pio, null, successfulSolverName);
    }

    SMTRuleApp(SMTRule rule, PosInOccurrence pio, ImmutableList<PosInOccurrence> unsatCore,
            String successfulSolverName) {
        super(rule, pio, unsatCore);
        this.title = "SMT: " + successfulSolverName;
        this.successfulSolverName = successfulSolverName;
    }

    @Override
    public SMTRuleApp replacePos(PosInOccurrence newPos) {
        return new SMTRuleApp(RULE, newPos, ifInsts, successfulSolverName);
    }

    @Override
    public boolean complete() {
        return true;
    }

    public String getTitle() {
        return title;
    }

    public String getSuccessfulSolverName() {
        return successfulSolverName;
    }

    @Override
    public PosInOccurrence posInOccurrence() {
        return pio;
    }

    @Override
    public BuiltInRule rule() {
        return RULE;
    }

    @Override
    public String displayName() {
        return title;
    }

    public static class SMTRule implements BuiltInRule {
        public static final Name name = new Name("SMTRule");

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
        public SMTRuleApp createApp(String successfulSolverName,
                ImmutableList<PosInOccurrence> unsatCore) {
            return new SMTRuleApp(this, null, unsatCore, successfulSolverName);
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
         * Create a new goal (to be closed in {@link Goal#apply(RuleApp)} directly afterwards)
         * with the same sequent as the given one.
         *
         * @param goal the Goal on which to apply <tt>ruleApp</tt>
         * @param services the Services with the necessary information about the java programs
         * @param ruleApp the rule application to be executed
         * @return a list with an identical goal as the given <tt>goal</tt>
         */
        @Override
        public ImmutableList<Goal> apply(Goal goal, Services services, RuleApp ruleApp) {
            if (goal.proof().getInitConfig().getJustifInfo().getJustification(RULE) == null) {
                goal.proof().getInitConfig().registerRule(RULE, () -> false);
            }
            return goal.split(1);
        }

        @Override
        public boolean isApplicableOnSubTerms() {
            return false;
        }

        @Override
        public String displayName() {
            return "SMT";
        }

        public String toString() {
            return displayName();
        }

        @Override
        public Name name() {
            return name;
        }

    }

    public SMTRuleApp setTitle(String title) {
        return new SMTRuleApp(RULE, pio, ifInsts, title);
    }

    @Override
    public SMTRuleApp setIfInsts(ImmutableList<PosInOccurrence> ifInsts) {
        setMutable(ifInsts);
        return this;
    }

    /**
     * Create a new RuleApp with the same pio (in this case, that will probably be null as the
     * SMT rule is applied to the complete sequent) as this one.
     * Add all top level formulas of the goal
     * to the RuleApp's ifInsts.
     *
     * @param goal the goal to instantiate the current RuleApp on
     * @return a new RuleApp with the same pio and all top level formulas of the goal as ifInsts
     */
    @Override
    public SMTRuleApp tryToInstantiate(Goal goal) {
        SMTRuleApp app = RULE.createApp(pio, goal.proof().getServices());
        Sequent seq = goal.sequent();
        List<PosInOccurrence> ifInsts = new ArrayList<>();
        for (SequentFormula ante : seq.antecedent()) {
            ifInsts.add(new PosInOccurrence(ante, PosInTerm.getTopLevel(), true));
        }
        for (SequentFormula succ : seq.succedent()) {
            ifInsts.add(new PosInOccurrence(succ, PosInTerm.getTopLevel(), false));
        }
        return app.setIfInsts(ImmutableList.fromList(ifInsts));
    }

}
