/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.proofmanagement.io;

/**
 * A logger for printing messages of given severity levels.
 *
 * @author Wolfram Pfeifer
 */
public interface Logger {
    /**
     * Prints a message to the logger.
     *
     * @param message the message to print
     */
    void print(String message);

    /**
     * Prints a message with the given severity level to the logger.
     *
     * @param logLevel the severity of the message
     * @param message the message to print
     */
    void print(LogLevel logLevel, String message);
}
