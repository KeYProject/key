/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule;

import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.proof.Goal;

import org.key_project.util.collection.ImmutableList;

/**
 * The rule application that is used when a goal is closed by means of an external solver. So far it
 * stores the rule that that has been used and a title containing some information for the user.
 * <p>
 * {@link de.uka.ilkd.key.smt.SMTRuleApp}
 */
public abstract class AbstractExternalSolverRuleApp extends AbstractBuiltInRuleApp {
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
    public String displayName() {
        return title;
    }

    /**
     * Interface for the rules of external solvers
     */
    public interface ExternalSolverRule extends BuiltInRule {
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

        @Override
        default boolean isApplicableOnSubTerms() {
            return false;
        }

        @Override
        String displayName();

        @Override
        String toString();
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
}
