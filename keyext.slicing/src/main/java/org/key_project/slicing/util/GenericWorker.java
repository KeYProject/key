/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.slicing.util;

import java.util.concurrent.Callable;
import java.util.function.Consumer;
import javax.swing.*;

/**
 * Generic background thread worker.
 *
 * @param <T> result of running the provided task
 * @author Arne Keller
 */
public class GenericWorker<T> extends SwingWorker<Void, Void> {
    /**
     * Task executed in this worker.
     */
    private final Callable<T> backgroundTask;
    /**
     * Callback if the task completed successfully.
     */
    private final Consumer<T> callback;
    /**
     * Callback if the task raised an exception.
     */
    private final Consumer<Exception> callbackError;

    /**
     * Create a new {@link GenericWorker}. Make sure to start it using {@link #execute()}!
     * The provided callbacks will be invoked on the AWT event dispatching thread.
     *
     * @param backgroundTask task to execute
     * @param callback callback on successful execution
     * @param callbackError callback if task raised an exception
     */
    public GenericWorker(Callable<T> backgroundTask, Consumer<T> callback,
            Consumer<Exception> callbackError) {
        this.backgroundTask = backgroundTask;
        this.callback = callback;
        this.callbackError = callbackError;
    }

    @Override
    protected Void doInBackground() throws Exception {
        try {
            T result = backgroundTask.call();
            SwingUtilities.invokeLater(() -> callback.accept(result));
        } catch (Exception e) {
            SwingUtilities.invokeLater(() -> callbackError.accept(e));
        }
        return null;
    }
}
