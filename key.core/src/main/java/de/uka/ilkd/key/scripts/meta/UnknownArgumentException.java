/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.scripts.meta;

/**
 * Exception thrown when an unrecognized argument is provided during script execution.
 * Occurs when a script passes an argument name that doesn't match any annotated field.
 *
 * @author Mattias Ulbrich
 */
public class UnknownArgumentException extends InjectionException {

    /**
     * An argument required exception with no cause (to display).
     *
     * @param message the respective String message to be passed.
     */
    public UnknownArgumentException(String message) {
        super(message);
    }
}
