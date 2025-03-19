/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.prover.impl;

import de.uka.ilkd.key.prover.ProverCore;
import de.uka.ilkd.key.prover.ProverTaskListener;
import de.uka.ilkd.key.prover.TaskFinishedInfo;
import de.uka.ilkd.key.prover.TaskStartedInfo.TaskKind;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

/**
 * Common class for provers which takes care of listener registration and task event propagation
 *
 * @author Richard Bubel
 */
public abstract class AbstractProverCore implements ProverCore {

    /** number of rules automatically applied */
    protected int countApplied = 0;

    /**
     * We use an immutable list to store listeners to allow for addition/removal within listener
     * code without causing a deadlock
     */
    private ImmutableList<ProverTaskListener> proverTaskObservers = ImmutableSLList.nil();


    /**
     * propagation method for the event that a task started
     *
     * @param maxSteps an int with the maximal number of steps to be performed by the current task
     */
    protected void fireTaskStarted(int maxSteps) {
        // no need to synchronize here as we use immutable list and hence
        // the add/remove task observer methods won't interfere
        for (final ProverTaskListener ptl : proverTaskObservers) {
            ptl.taskStarted(
                new DefaultTaskStartedInfo(TaskKind.Strategy, PROCESSING_STRATEGY, maxSteps));
        }
    }

    /**
     * propagation of task progress information to be displayed e.g. in a progress bar
     */
    protected void fireTaskProgress() {
        // no need to synchronize here as we use immutable list and hence
        // the add/remove task observer methods won't interfere
        for (final ProverTaskListener ptl : proverTaskObservers) {
            ptl.taskProgress(countApplied);
        }
    }

    /**
     * propagation method for the event that a task has finished
     *
     * @param info an information object about the work done by the task e.g. number of applied
     *        rules
     */
    protected void fireTaskFinished(TaskFinishedInfo info) {
        // no need to synchronize here as we use immutable list and hence
        // the add/remove task observer methods won't interfere
        for (final ProverTaskListener ptl : proverTaskObservers) {
            ptl.taskFinished(info);
        }
    }

    /**
     * adds a listener to the prover
     *
     * @param observer the listener
     */
    @Override
    public void addProverTaskObserver(ProverTaskListener observer) {
        synchronized (proverTaskObservers) {
            proverTaskObservers = proverTaskObservers.prepend(observer);
        }
    }

    /**
     * removes a listener from the prover
     *
     * @param observer the listener
     */
    @Override
    public void removeProverTaskObserver(ProverTaskListener observer) {
        synchronized (proverTaskObservers) {
            proverTaskObservers = proverTaskObservers.removeAll(observer);
        }
    }

}
