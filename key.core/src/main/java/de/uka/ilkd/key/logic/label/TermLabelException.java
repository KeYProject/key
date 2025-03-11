/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic.label;

/**
 * An exception which can be thrown by the term label system.
 *
 * <p>
 * {@link TermLabelFactory} methods can throw an instance if the requested term label cannot be
 * created.
 *
 * <p>
 * {@link TermLabelManager} can throw this if a requested label name has not been registered.
 *
 * @author mattias ulbrich
 */
public class TermLabelException extends Exception {
    private static final long serialVersionUID = -6012867553428479252L;

    public TermLabelException() {
        super();
    }

    public TermLabelException(String message, Throwable cause) {
        super(message, cause);
    }

    public TermLabelException(String message) {
        super(message);
    }

    public TermLabelException(Throwable cause) {
        super(cause);
    }

}
