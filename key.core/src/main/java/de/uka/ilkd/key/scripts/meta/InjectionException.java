/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.scripts.meta;

import de.uka.ilkd.key.scripts.ScriptException;

/**
 *
 *
 * @author Alexander Weigl
 * @version 1 (02.05.17)
 */
public class InjectionException extends ScriptException {
    /**
     * An injection reflection exception with no cause (to display).
     *
     * @param message the respective String message to be passed.
     */
    public InjectionException(String message) {
        super(message);
    }

    /**
     * An injection exception with a cause to be displayed.
     *
     * @param message the respective String message to be passed.
     * @param cause the cause of the exception.
     */
    public InjectionException(String message, Throwable cause) {
        super(message, cause);
    }
}
