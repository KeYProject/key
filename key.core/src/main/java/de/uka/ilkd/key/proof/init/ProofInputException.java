/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof.init;

/**
 * Reading prover input failed
 */
public class ProofInputException extends Exception {
    private static final long serialVersionUID = 1028674319098864943L;

    public ProofInputException(Exception e) {
        this(e.getMessage(), e);
    }

    public ProofInputException(String s) {
        this(s, null);
    }

    public ProofInputException(String message, Throwable cause) {
        super(message, cause);
    }
}
