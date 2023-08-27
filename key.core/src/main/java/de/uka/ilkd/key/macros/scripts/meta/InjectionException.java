/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.macros.scripts.meta;

/**
 *
 *
 * @author Alexander Weigl
 * @version 1 (02.05.17)
 */
public class InjectionException extends Exception {

    private static final long serialVersionUID = 4922701573932568352L;
    private final ProofScriptArgument<?> argument;

    /**
     * An injection reflection exception with no cause (to display).
     *
     * @param message the respective String message to be passed.
     * @param argument the proof script argument.
     */
    public InjectionException(String message, ProofScriptArgument<?> argument) {
        super(message);
        this.argument = argument;
    }

    /**
     * An injection exception with a cause to be displayed.
     *
     * @param message the respective String message to be passed.
     * @param cause the cause of the exception.
     * @param argument the proof script argument.
     */
    public InjectionException(String message, Throwable cause, ProofScriptArgument<?> argument) {
        super(message, cause);
        this.argument = argument;
    }

    /**
     * Get the (proof script) argument of this injection exception.
     *
     * @return the proof script argument.
     */
    public ProofScriptArgument<?> getArgument() {
        return argument;
    }
}
