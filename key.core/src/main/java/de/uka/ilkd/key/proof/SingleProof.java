/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof;

import java.util.Collections;
import java.util.List;

import de.uka.ilkd.key.proof.mgt.ProofStatus;

public class SingleProof extends ProofAggregate {

    private final Proof proof;

    public SingleProof(Proof p, String name) {
        super(name);
        assert p != null;
        this.proof = p;
    }

    @Override
    public ProofStatus getStatus() {
        return proof.mgt().getStatus();
    }

    @Override
    public Proof[] getProofs() {
        return new Proof[] { proof };
    }

    @Override
    public boolean equals(Object o) {
        if (!super.equals(o)) {
            return false;
        }
        final SingleProof other = (SingleProof) o;

        return proof == other.proof;
    }


    @Override
    public int hashCode() {
        return super.hashCode() + proof.hashCode();
    }

    @Override
    public int size() {
        return 1;
    }

    @Override
    public List<ProofAggregate> getChildren() {
        return Collections.emptyList();
    }

    @Override
    public ProofAggregate getChildrenAt(int i) {
        throw new IndexOutOfBoundsException("Tried to access child of SingleProof");
    }
}
