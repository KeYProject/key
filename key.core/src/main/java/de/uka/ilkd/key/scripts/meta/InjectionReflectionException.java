/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.scripts.meta;

/**
 * Exception thrown when reflection errors occur during value injection.
 * Wraps reflective operation failures that happen while accessing or setting fields.
 *
 * @author Alexander Weigl
 * @version 1 (02.05.17)
 */
public class InjectionReflectionException extends InjectionException {
    /**
     * An injection reflection exception with no cause (to display).
     *
     * @param message the respective String message to be passed.
     */
    public InjectionReflectionException(String message) {
        super(message);
    }

    /**
     * An injection reflection exception with a cause to be displayed.
     *
     * @param message the respective String message to be passed.
     * @param cause the cause of the exception.
     */
    public InjectionReflectionException(String message, Throwable cause) {
        super(message, cause);
    }
}
