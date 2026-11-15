/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.testgen.fx;

import org.jspecify.annotations.NullMarked;

/**
 * The log/report sink of the FX run dialogs, counterpart of the lifecycle-logger slots of the
 * Swing {@code TGInfoDialog} and {@code SolverListener}. The reflective bridge
 * ({@link TestgenReflectionF}) translates the {@code TestGenerationLifecycleListener} and
 * {@code SolverLauncherListener} events of the key.core.testgen machinery into these three
 * callbacks; the dialogs append the messages to their {@code TextArea} (marshalled to the FX
 * thread).
 */
@NullMarked
interface LogSinkF {

    /** Appends one log line (without trailing newline). */
    void writeln(String message);

    /** Reports a failure; the callers log the whole stack trace via the module logger. */
    default void error(Throwable throwable) {
    }

    /** Called when the run reported its {@code finish} event (generation only). */
    default void finished() {
    }
}
