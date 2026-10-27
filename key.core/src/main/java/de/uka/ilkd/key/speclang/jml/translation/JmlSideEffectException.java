/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.speclang.jml.translation;

/**
 * Thrown by the {@link JmlSideEffectChecker} when a JML specification expression contains a
 * construct with a potential side effect (assignments, increments/decrements, object or array
 * creation) that is not expressible in KeY's JML term grammar and must therefore be rejected
 * instead of being silently skipped or mis-translated.
 */
public class JmlSideEffectException extends RuntimeException {

    private static final long serialVersionUID = -2704872108266041441L;

    public JmlSideEffectException(String message) {
        super(message);
    }
}
