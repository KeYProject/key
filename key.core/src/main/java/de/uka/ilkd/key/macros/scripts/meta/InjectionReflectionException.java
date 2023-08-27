/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.macros.scripts.meta;

/**
 * @author Alexander Weigl
 * @version 1 (02.05.17)
 */
public class InjectionReflectionException extends InjectionException {

    private static final long serialVersionUID = -5062920998506967420L;

    /**
     * An injection reflection exception with no cause (to display).
     *
     * @param message the respective String message to be passed.
     * @param argument the proof script argument.
     */
    public InjectionReflectionException(String message, ProofScriptArgument<?> argument) {
        super(message, argument);
    }

    /**
     * An injection reflection exception with a cause to be displayed.
     *
     * @param message the respective String message to be passed.
     * @param cause the cause of the exception.
     * @param argument the proof script argument.
     */
    public InjectionReflectionException(String message, Throwable cause,
            ProofScriptArgument<?> argument) {
        super(message, cause, argument);
    }
}
