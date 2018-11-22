package de.uka.ilkd.key.prover;

import org.key_project.util.collection.ImmutableList;

import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.prover.impl.ApplyStrategyInfo;
import de.uka.ilkd.key.settings.StrategySettings;

public interface ProverCore {

	ApplyStrategyInfo start(Proof proof, Goal goal);

	ApplyStrategyInfo start(Proof proof, ImmutableList<Goal> goals);

	ApplyStrategyInfo start(Proof proof, ImmutableList<Goal> goals, StrategySettings stratSet);

	/**
	 * This entry point to the proof may provide inconsistent data. The
	 * properties within the proof may differ to the explicit data. This is
	 * discouraged.
	 *
	 * @return
	 */
	ApplyStrategyInfo start(Proof proof, ImmutableList<Goal> goals, int maxSteps, long timeout,
			boolean stopAtFirstNonCloseableGoal);

	void addProverTaskObserver(ProverTaskListener observer);

	void removeProverTaskObserver(ProverTaskListener observer);

	/**Used by, e.g., {@code InteractiveProver.clear()} in order to prevent memory leaking.
	 * When a proof obligation is abandoned all references to the proof must be reset.
	 * @author gladisch */
	void clear();

	/**
	 * Returns true iff the last run has been stopped due to a received
	 * {@link InterruptedException}. This exception would have been swallowed by
	 * the system. However, the cancelled flag is set in this case which allows
	 * detection of such a condition.
	 *
	 * @return whether the last run has been interrupted
	 */
	boolean hasBeenInterrupted();

}