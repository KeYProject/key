/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule;

import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.proof.Goal;

import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.util.collection.ImmutableList;

/**
 * Interface for the rules of external solvers
 */
public interface ExternalSolverRule extends BuiltInRule {
    <T extends ExternalSolverRule> AbstractExternalSolverRuleApp<T> createApp(
            String successfulSolverName);

    /**
     * Create a new rule application with the given solver name and unsat core.
     *
     * @param successfulSolverName solver that produced this result
     * @param unsatCore formulas required to prove the result
     * @return rule application instance
     */
    <T extends ExternalSolverRule> AbstractExternalSolverRuleApp<T> createApp(
            String successfulSolverName, ImmutableList<PosInOccurrence> unsatCore);

    @Override
    IBuiltInRuleApp createApp(PosInOccurrence pos, TermServices services);


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
