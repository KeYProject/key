/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.prover;

import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.prover.impl.ApplyStrategyInfo;
import de.uka.ilkd.key.settings.StrategySettings;

import org.key_project.util.collection.ImmutableList;

public interface ProverCore {

    /**
     * constant used by some listeners to determine if a proof macro is running
     */
    String PROCESSING_STRATEGY = "Processing Strategy";

    /**
     * starts a proof search for a given goals using the given strategy settings instead the ones
     * configures in the proof
     *
     * @param proof the Proof instance
     * @param goal the goal to prove
     * @return an information object about the performed work (e.g. number of rules applied)
     */
    ApplyStrategyInfo start(Proof proof, Goal goal);

    /**
     * starts a proof search for a set of goals using the given strategy settings instead the ones
     * configures in the proof
     *
     * @param proof the Proof instance
     * @param goals list of goals to prove
     * @return an information object about the performed work (e.g. number of rules applied)
     */
    ApplyStrategyInfo start(Proof proof, ImmutableList<Goal> goals);

    /**
     * starts a proof search for a set of goals using the given strategy settings instead the ones
     * configures in the proof
     *
     * @param proof the Proof instance
     * @param goals list of goals to prove
     * @param stratSet the strategy settings to use
     * @return an information object about the performed work (e.g. number of rules applied)
     */
    ApplyStrategyInfo start(Proof proof, ImmutableList<Goal> goals, StrategySettings stratSet);

    /**
     * This entry point to the proof may provide inconsistent data. The properties within the proof
     * may differ to the explicit data. This is discouraged. starts a proof search for a set of
     * goals
     *
     * @param proof the Proof instance
     * @param goals list of goals to prove
     * @param maxSteps an int with the maximal number of rule applications to be performed
     * @param timeout a long with a timeout when tyo stop the proof search at latest
     * @param stopAtFirstNonCloseableGoal true if the prover shall stop at the first encountered
     *        non-closable goal
     * @return an information object about the performed work (e.g. number of rules applied)
     */
    ApplyStrategyInfo start(Proof proof, ImmutableList<Goal> goals, int maxSteps, long timeout,
            boolean stopAtFirstNonCloseableGoal);

    /**
     * adds a task listener
     *
     * @param observer the listener to add
     */
    void addProverTaskObserver(ProverTaskListener observer);

    /**
     * removes a task listener
     *
     * @param observer the listener to remove
     */
    void removeProverTaskObserver(ProverTaskListener observer);

    /**
     * Used by, e.g., {@code InteractiveProver.clear()} in order to prevent memory leaking. When a
     * proof obligation is abandoned all references to the proof must be reset.
     *
     * @author gladisch
     */
    void clear();

    /**
     * Returns true iff the last run has been stopped due to a received
     * {@link InterruptedException}. This exception would have been swallowed by the system.
     * However, the cancelled flag is set in this case which allows detection of such a condition.
     *
     * @return whether the last run has been interrupted
     */
    boolean hasBeenInterrupted();

}
