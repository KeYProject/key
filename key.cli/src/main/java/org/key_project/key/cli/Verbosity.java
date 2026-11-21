/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.cli;

/**
 * Verbosity levels for the console logging of the headless CLI.
 * <p>
 * The levels mirror the CLI verbosity levels used by the KeY user interface (see
 * {@code de.uka.ilkd.key.ui.Verbosity}) with {@code ERROR} acting as the default
 * for headless batch runs.
 */
public interface Verbosity {
    /// No logging at all.
    int SILENT = 0;
    /// Only error messages.
    int ERROR = 1;
    /// Informational messages and errors.
    int INFO = 2;
    /// Debug messages and everything below.
    int DEBUG = 3;
    /// Trace messages and everything below.
    int TRACE = 4;
}
