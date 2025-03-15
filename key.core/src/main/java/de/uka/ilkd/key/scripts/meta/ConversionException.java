/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.scripts.meta;

/**
 * This exception signals that the conversion to the required data type could not be applied.
 *
 * @author Alexander Weigl
 * @version 1 (02.05.17)
 */
public class ConversionException extends InjectionException {
    /**
     * A conversion exception with no cause (to display).
     *
     * @param message the respective String message to be passed.
     */
    public ConversionException(String message) {
        super(message);
    }

    /**
     * A conversion exception with a cause to be displayed.
     *
     * @param message the respective String message to be passed.
     * @param cause the cause of the exception.
     */
    public ConversionException(String message, Throwable cause) {
        super(message, cause);
    }
}
