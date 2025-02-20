package org.keyproject.key.api.data;

import de.uka.ilkd.key.proof.Proof;

public record ProofStatus(KeyIdentifications.ProofId id, int openGoals, int closedGoals) {
    public static ProofStatus from(KeyIdentifications.ProofId id, Proof proof) {
        return new ProofStatus(id, proof.openGoals().size(), proof.closedGoals().size());
    }
}
