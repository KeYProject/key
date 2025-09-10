/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.scripts.meta;

/**
 * Signals if an unknown/unexpected argument has been provided for injection.
 *
 * @author Mattias Ulbrich
 */
public class UnknownArgumentException extends InjectionException {
    public UnknownArgumentException(String message) {
        super(message);
    }
}
