package de.uka.ilkd.key.prover;

/**
 * Listener for longer tasks, which may be run in a separate worker thread. Examples: proof loading,
 * processing strategies
 */
public interface ProverTaskListener {
    /**

     */
    void taskStarted(TaskStartedInfo info);

    /**
     * Called when progress is made on a task.
     *
     * This method is called after every single step of the task
     *
     * @param position indicates how much work has been done relative to the value of {@code size}
     *        passed in {@link #taskStarted(TaskStartedInfo)}.
     */
    void taskProgress(int position);


    /**
     * Called when a task is finished.
     *
     * @param info a TaskFinishedInfo object with additional information
     */
    void taskFinished(TaskFinishedInfo info);
}
