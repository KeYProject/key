/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule;

import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.util.collection.ImmutableList;

import org.jspecify.annotations.NullMarked;

/**
 * The rule application that is used when a goal is closed by means of an external solver. So far it
 * stores the rule that that has been used and a title containing some information for the user.
 * <p>
 * {@link de.uka.ilkd.key.smt.SMTRuleApp}
 */
@NullMarked
public abstract class AbstractExternalSolverRuleApp<T extends ExternalSolverRule>
        extends AbstractBuiltInRuleApp<T> {

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
    protected AbstractExternalSolverRuleApp(T rule, PosInOccurrence pio,
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
     * Sets the title (needs to create a new instance for this)
     *
     * @param title new title for rule app
     * @return copy of this with the new title
     */
    public abstract AbstractExternalSolverRuleApp<T> setTitle(String title);

    @Override
    public AbstractExternalSolverRuleApp<T> setAssumesInsts(
            ImmutableList<PosInOccurrence> ifInsts) {
        setMutable(ifInsts);
        return this;
    }
}
