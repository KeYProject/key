/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.scripts;

/**
 * Thrown if during the execution of a command, the proof is already closed. May or may not lead to
 * exceptional termination of the whole script based on the <code>@failonclosed</code> setting.
 *
 * @author Dominic Steinhoefel
 */
public class ProofAlreadyClosedException extends ScriptException {
    private static final long serialVersionUID = 1L;

    public ProofAlreadyClosedException(String message) {
        super(message);
    }
}
