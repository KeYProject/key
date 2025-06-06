/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.prover.engine;

import java.util.List;
import java.util.concurrent.CopyOnWriteArrayList;

import org.key_project.prover.proof.ProofGoal;
import org.key_project.prover.proof.ProofObject;

/// Common class for provers which takes care of listener registration and task event propagation.
///
/// @author Richard Bubel
public abstract class AbstractProverCore<P extends ProofObject<G>, G extends ProofGoal<G>>
        implements ProverCore<P, G> {

    /// number of rules automatically applied
    protected int countApplied = 0;

    /// We use an immutable list to store listeners to allow for addition/removal within listener
    /// code without causing a deadlock
    private final List<ProverTaskListener> proverTaskObservers = new CopyOnWriteArrayList<>();

    /// propagation method for the event that a task started
    ///
    /// @param startedInfo an information object describing the started task
    /// (may contain, for example, the maximal number of steps
    /// to be performed by the current task)
    protected void fireTaskStarted(TaskStartedInfo startedInfo) {
        // proverTaskObserver is a thread safe implementation, hence we do not need
        // to synchronize here
        for (final ProverTaskListener ptl : proverTaskObservers) {
            ptl.taskStarted(startedInfo);
        }
    }

    /// propagation of task progress information to be displayed e.g. in a progress bar
    protected void fireTaskProgress() {
        // proverTaskObserver is a thread safe implementation, hence we do not need
        // to synchronize here
        for (final ProverTaskListener ptl : proverTaskObservers) {
            ptl.taskProgress(countApplied);
        }
    }

    /// propagation method for the event that a task has finished
    ///
    /// @param info an information object about the work done by the task e.g. number of applied
    /// rules
    protected void fireTaskFinished(TaskFinishedInfo info) {
        // proverTaskObserver is a thread safe implementation, hence we do not need
        // to synchronize here
        for (final ProverTaskListener ptl : proverTaskObservers) {
            ptl.taskFinished(info);
        }
    }

    /// adds a listener to the prover
    ///
    /// @param observer the listener
    @Override
    public void addProverTaskObserver(ProverTaskListener observer) {
        // proverTaskObserver is a thread safe implementation, hence we do not need
        // to synchronize here
        proverTaskObservers.add(observer);
    }

    /// removes a listener from the prover
    ///
    /// @param observer the listener
    @Override
    public void removeProverTaskObserver(final ProverTaskListener observer) {
        // proverTaskObserver is a thread safe implementation, hence we do not need
        // to synchronize here
        proverTaskObservers.removeIf(o -> o.equals(observer));
    }

}
