/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.util;

/**
 * Exception used by {@link CommandLine}.
 *
 * @see CommandLine
 */
public class CommandLineException extends Exception {

    private static final long serialVersionUID = 3286607114115333522L;

    /**
     * Instantiates a new command line exception without message.
     */
    public CommandLineException() {
        super();
    }

    /**
     * Instantiates a new command line exception.
     *
     * @param message an error message
     * @param cause the exception causing this exception
     */
    public CommandLineException(String message, Throwable cause) {
        super(message, cause);
    }

    /**
     * Instantiates a new command line exception.
     *
     * @param message an error message
     */
    public CommandLineException(String message) {
        super(message);
    }

    /**
     * Instantiates a new command line exception.
     *
     * @param cause the exception causing this exception
     */
    public CommandLineException(Throwable cause) {
        super(cause);
    }

}
