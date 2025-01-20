/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.service;

/**
 * An error handler that receives exceptions from services, reports them to the user and may react
 * upon them. The using context should provide a mean to resume processing if an exception can be
 * handled.
 * <p>
 * Error handlers are registered as model update listeners so that they can collect some errors and
 * still provide some fallback strategy when the current analysis phase is complete.
 * <p>
 * Error handlers may allow to resume a certain amount of times before it stops the analysis. The
 * behavior in that case depends on the current handler and may include system termination or
 * falling back to a secure state. Specific error handlers may also tolerate certain kinds of
 * errors.
 *
 * @since 0.71
 */
public interface ErrorHandler extends ModelUpdateListener {

    /**
     * Returns the number of errors that this error handler accepts before stopping the current
     * analysis.
     */
    int getErrorThreshold();

    /**
     * Sets the number of errors that this error handler accepts before stopping the current
     * analysis. Setting this value to zero results in a fail at once behavior.
     */
    void setErrorThreshold(int maxCount);

    /**
     * Handles exceptions and may return so that the callee can attempt to resume or fail, throwing
     * the given error as an exception.
     *
     * @param e an error cause.
     * @throws RuntimeException the given exception might be wrapped in a RunTimeException and be
     *         thrown.
     */
    void reportError(Exception e) throws RuntimeException;
}
