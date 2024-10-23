/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule;

import java.util.ArrayList;
import java.util.List;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.proof.Goal;

import org.key_project.logic.Name;
import org.key_project.util.collection.ImmutableList;

/**
 * The rule application that is used when a goal is closed by means of an external solver. So far it
 * stores the rule that that has been used and a title containing some information for the user.
 * <p>
 * {@link de.uka.ilkd.key.smt.SMTRuleApp}
 */
public abstract class AbstractExternalSolverRuleApp extends AbstractBuiltInRuleApp {
    protected final ExternalSolverRule rule;
    protected final String title;
    protected final String successfulSolverName;

    /**
     * Creates a new AbstractExternalSolverRuleApp,
     *
     * @param rule the ExternalSolverRule to apply
     * @param pio the position in the term to apply the rule to
     * @param unsatCore an unsat core consisting of the formulas that are needed to prove the goal
     *        (optional null)
     * @param successfulSolverName the name of the solver used to find the proof
     * @param title the title of this rule app
     */
    protected AbstractExternalSolverRuleApp(ExternalSolverRule rule, PosInOccurrence pio,
            ImmutableList<PosInOccurrence> unsatCore,
            String successfulSolverName, String title) {
        super(rule, pio, unsatCore);
        this.rule = rule.newRule();
        this.title = title;
        this.successfulSolverName = successfulSolverName;
    }

    /**
     * Gets the title of this rule application
     *
     * @return title of this application
     */
    public String getTitle() {
        return title;
    }

    /**
     * Gets the name of the successful solver
     *
     * @return name of the successful solver
     */
    public String getSuccessfulSolverName() {
        return successfulSolverName;
    }

    @Override
    public BuiltInRule rule() {
        return rule;
    }

    @Override
    public String displayName() {
        return title;
    }

    /**
     * Interface for the rules of external solvers
     */
    public interface ExternalSolverRule extends BuiltInRule {
        Name name = new Name("ExternalSolverRule");

        ExternalSolverRule newRule();

        AbstractExternalSolverRuleApp createApp(String successfulSolverName);

        /**
         * Create a new rule application with the given solver name and unsat core.
         *
         * @param successfulSolverName solver that produced this result
         * @param unsatCore formulas required to prove the result
         * @return rule application instance
         */
        AbstractExternalSolverRuleApp createApp(String successfulSolverName,
                ImmutableList<PosInOccurrence> unsatCore);

        @Override
        AbstractExternalSolverRuleApp createApp(PosInOccurrence pos, TermServices services);


        @Override
        default boolean isApplicable(Goal goal, PosInOccurrence pio) {
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
        default ImmutableList<Goal> apply(Goal goal, Services services, RuleApp ruleApp) {
            if (goal.proof().getInitConfig().getJustifInfo().getJustification(newRule()) == null) {
                goal.proof().getInitConfig().registerRule(newRule(), () -> false);
            }
            return goal.split(1);
        }

        @Override
        default boolean isApplicableOnSubTerms() {
            return false;
        }

        @Override
        default String displayName() {
            return "ExternalSolver";
        }

        @Override
        String toString();

        @Override
        default Name name() {
            return name;
        }

    }

    /**
     * Sets the title (needs to create a new instance for this)
     *
     * @param title new title for rule app
     * @return copy of this with the new title
     */
    public abstract AbstractExternalSolverRuleApp setTitle(String title);

    @Override
    public AbstractExternalSolverRuleApp setIfInsts(ImmutableList<PosInOccurrence> ifInsts) {
        setMutable(ifInsts);
        return this;
    }

    /**
     * Create a new RuleApp with the same pio (in this case, that will probably be null as the
     * AbstractExternalSolver rule is applied to the complete sequent) as this one.
     * Add all top level formulas of the goal
     * to the RuleApp's ifInsts.
     *
     * @param goal the goal to instantiate the current RuleApp on
     * @return a new RuleApp with the same pio and all top level formulas of the goal as ifInsts
     */
    @Override
    public AbstractExternalSolverRuleApp tryToInstantiate(Goal goal) {
        AbstractExternalSolverRuleApp app = rule.createApp(pio, goal.proof().getServices());
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
