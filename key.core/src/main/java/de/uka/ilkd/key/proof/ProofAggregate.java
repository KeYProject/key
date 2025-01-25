/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof;

import java.util.List;
import java.util.Objects;

import de.uka.ilkd.key.proof.mgt.ProofEnvironment;
import de.uka.ilkd.key.proof.mgt.ProofStatus;

import org.jspecify.annotations.Nullable;

public abstract class ProofAggregate {

    private final String name;

    protected ProofAggregate(String name) {
        this.name = name;
    }

    public static ProofAggregate createProofAggregate(ProofAggregate[] proofs, String name) {
        if (proofs.length > 1) {
            return new CompoundProof(name, proofs);
        } else {
            return proofs[0];
        }
    }

    public static @Nullable ProofAggregate createProofAggregate(Proof[] proofs, String name) {
        if (proofs.length == 0) {
            return null; // needed for tests
        }
        if (proofs.length > 1) {
            SingleProof[] singles = new SingleProof[proofs.length];
            for (int i = 0; i < proofs.length; i++) {
                singles[i] = new SingleProof(proofs[i], name);
            }
            return new CompoundProof(name, singles);
        } else {
            return new SingleProof(proofs[0], name);
        }
    }

    public static ProofAggregate createProofAggregate(Proof proof, String name) {
        return new SingleProof(proof, name);
    }

    public abstract Proof @Nullable [] getProofs();

    public @Nullable Proof getFirstProof() {
        return getProofs() != null && getProofs().length >= 1 ? getProofs()[0] : null;
    }

    public void setProofEnv(ProofEnvironment env) {
        Proof[] proofs = getProofs();
        if (proofs != null) {
            for (Proof proof : proofs) {
                proof.setEnv(env);
            }
        }
    }

    public abstract int size();

    public String description() {
        return name;
    }

    @Override
    public boolean equals(@Nullable Object o) {
        if (o == null || o.getClass() != this.getClass()) {
            return false;
        }
        final ProofAggregate other = (ProofAggregate) o;

        return size() == other.size() && name.equals(other.name);
    }

    @Override
    public int hashCode() {
        return 7 * size() + 17 * name.hashCode();
    }

    public String toString() {
        return name;
    }

    public abstract ProofStatus getStatus();

    public abstract List<ProofAggregate> getChildren();

    public abstract ProofAggregate getChildrenAt(int i);

    public Proof getProof(int proofNum) {
        return Objects.requireNonNull(getProofs())[proofNum];
    }


}
