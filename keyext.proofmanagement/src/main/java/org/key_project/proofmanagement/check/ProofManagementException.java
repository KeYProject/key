/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.proofmanagement.check;

public class ProofManagementException extends Exception {
    public ProofManagementException(String message) {
        super(message);
    }

    public ProofManagementException(String message, Throwable cause) {
        super(message, cause);
    }
}
