/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.symbolic_execution.strategy.breakpoint;

import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.settings.StrategySettings;

import org.key_project.prover.engine.StopCondition;
import org.key_project.prover.proof.ProofGoal;
import org.key_project.prover.rules.RuleApp;

/**
 * Defines the basic functionality of a breakpoint.
 *
 * @author Martin Hentschel
 */
public interface IBreakpoint {
    /**
     * Checks if the Breakpoint is enabled.
     *
     * @return true if Breakpoint is enabled
     */
    boolean isEnabled();

    /**
     * This method is called from
     * {@link StopCondition#isGoalAllowed(ProofGoal, int, long, long, int)} and can be used to
     * update the state of the {@link IBreakpoint}.
     *
     * @param goal The current {@link Goal} on which the next rule will be applied.
     * @param maxApplications The defined maximal number of rules to apply. Can be different to
     *        {@link StrategySettings#getMaxSteps()} in side proofs.
     * @param timeout The defined timeout in ms or {@code -1} if disabled. Can be different to
     *        {@link StrategySettings#getTimeout()} in side proofs.
     * @param startTime The timestamp when the apply strategy has started, computed via
     *        {@link System#currentTimeMillis()}
     * @param countApplied The number of already applied rules.
     */
    void updateState(Goal goal, int maxApplications, long timeout, long startTime,
            int countApplied);

    /**
     * Determines if the breakpoint represented by this BreakpointStopConition is triggered.
     * Override this method in order to suspend execution when a breakpoint is hit.
     *
     * @param activeStatement the activeStatement of the node
     * @param ruleApp the applied {@link RuleApp}
     * @param node the current node
     * @return true if execution should hold
     */
    boolean isBreakpointHit(SourceElement activeStatement,
            RuleApp ruleApp, Node node);
}
