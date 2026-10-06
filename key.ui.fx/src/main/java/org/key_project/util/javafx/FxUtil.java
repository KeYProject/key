/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.util.javafx;

import java.util.concurrent.Callable;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.FutureTask;

import javafx.application.Platform;

/**
 * Utilities for working with the JavaFX Application Thread (the FX analogue of
 * {@code org.key_project.util.java.SwingUtil} in the Swing module {@code key.ui}).
 * <p>
 * All UI state must be mutated on the JavaFX Application Thread. Use these helpers to marshal
 * between background threads (prover, SMT, I/O) and the UI.
 */
public final class FxUtil {

    private FxUtil() {
    }

    /**
     * @return whether the calling thread is the JavaFX Application Thread
     */
    public static boolean isFxThread() {
        return Platform.isFxApplicationThread();
    }

    /**
     * Runs the given {@link Runnable} on the JavaFX Application Thread. If the calling thread
     * already is the JavaFX Application Thread, the runnable is executed immediately.
     *
     * @param runnable the code to run on the FX thread
     */
    public static void runLater(Runnable runnable) {
        if (isFxThread()) {
            runnable.run();
        } else {
            Platform.runLater(runnable);
        }
    }

    /**
     * Runs the given {@link Runnable} on the JavaFX Application Thread and blocks until it has
     * been executed.
     *
     * @param runnable the code to run on the FX thread
     * @throws IllegalStateException if the runnable throws an exception
     */
    public static void runAndWait(Runnable runnable) {
        if (isFxThread()) {
            runnable.run();
            return;
        }
        FutureTask<Void> task = new FutureTask<>(runnable, null);
        Platform.runLater(task);
        try {
            task.get();
        } catch (InterruptedException e) {
            Thread.currentThread().interrupt();
            throw new IllegalStateException("Interrupted while waiting for the FX thread", e);
        } catch (ExecutionException e) {
            throw new IllegalStateException("Exception on the FX thread", e.getCause());
        }
    }

    /**
     * Runs the given {@link Callable} on the JavaFX Application Thread, blocks until the result
     * is available and returns it.
     *
     * @param callable the computation to run on the FX thread
     * @param <T> the result type
     * @return the computed value
     * @throws IllegalStateException if the callable throws an exception
     */
    public static <T> T callAndWait(Callable<T> callable) {
        if (isFxThread()) {
            try {
                return callable.call();
            } catch (Exception e) {
                throw new IllegalStateException("Exception on the FX thread", e);
            }
        }
        FutureTask<T> task = new FutureTask<>(callable);
        Platform.runLater(task);
        try {
            return task.get();
        } catch (InterruptedException e) {
            Thread.currentThread().interrupt();
            throw new IllegalStateException("Interrupted while waiting for the FX thread", e);
        } catch (ExecutionException e) {
            throw new IllegalStateException("Exception on the FX thread", e.getCause());
        }
    }

    /**
     * Asserts that the calling thread is the JavaFX Application Thread. Use this as a defensive
     * check at the entry points of UI-updating methods.
     *
     * @throws IllegalStateException if called from a non-FX thread
     */
    public static void assertFxThread() {
        if (!isFxThread()) {
            throw new IllegalStateException(
                "Must be called on the JavaFX Application Thread, but was called on "
                    + Thread.currentThread().getName());
        }
    }
}
