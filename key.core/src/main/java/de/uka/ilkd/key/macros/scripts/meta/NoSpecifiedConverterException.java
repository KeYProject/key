/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.macros.scripts.meta;

/**
 * Indicates a missing converter.
 * <p>
 * This is exception is raised if {@link StringConverter} is found for string to the desired type
 * {@code T}. The desired type is in the stored {@link ProofScriptArgument}.
 *
 * @author Alexander Weigl
 * @version 1 (02.05.17)
 */
public class NoSpecifiedConverterException extends InjectionException {

    private static final long serialVersionUID = -4808272101189047873L;

    /**
     * Creates an exception with the given {@code message} and {@code argument}.
     *
     * @param message a non-null string
     * @param argument the argument for which the conversion failed
     */
    public NoSpecifiedConverterException(String message, ProofScriptArgument<?> argument) {
        super(message, argument);
    }

    /**
     * Creates an exception with the given arguments.
     *
     * @param message a non-null string
     * @param cause a cause of this exception
     * @param argument the argument for which the conversion failed
     */
    public NoSpecifiedConverterException(String message, Throwable cause,
            ProofScriptArgument<?> argument) {
        super(message, cause, argument);
    }
}
