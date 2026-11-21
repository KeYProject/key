/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.cli.prove;

/**
 * Signals a conflict between the requested proof-file output ({@code --proof}) and the number of
 * selected contracts (§3 of the headless interface spec): {@code --proof} names a single file,
 * so it cannot be used when several contracts are selected ({@code --proof-dir} applies).
 * {@link ProveCommand} maps it to an input error (exit {@code 3}).
 */
public final class ProofOutputConflictException extends RuntimeException {

    /**
     * Creates the exception with the user-facing message.
     *
     * @param message the human-readable conflict description
     */
    public ProofOutputConflictException(String message) {
        super(message);
    }
}
