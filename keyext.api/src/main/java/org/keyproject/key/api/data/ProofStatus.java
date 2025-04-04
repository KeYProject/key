/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.keyproject.key.api.data;

import de.uka.ilkd.key.proof.Proof;

public record ProofStatus(KeyIdentifications.ProofId id, int openGoals, int closedGoals) implements KeYDataTransferObject {
    public static ProofStatus from(KeyIdentifications.ProofId id, Proof proof) {
        return new ProofStatus(id, proof.openGoals().size(), proof.closedGoals().size());
    }
}
