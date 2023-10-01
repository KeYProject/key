/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof.mgt;


public enum ProofStatus {
    /**
     * Proof is open.
     */
    OPEN,
    /**
     * Proof is closed, but depends on other contracts.
     */
    CLOSED_BUT_LEMMAS_LEFT,
    /**
     * Proof is closed, some goals are closed by reference to the cache.
     */
    CLOSED_BY_CACHE,
    /**
     * Proof is closed.
     */
    CLOSED;

    public boolean getProofClosed() {
        return this == CLOSED;
    }

    public boolean getProofClosedButLemmasLeft() {
        return this == CLOSED_BUT_LEMMAS_LEFT;
    }

    public boolean getProofClosedByCache() {
        return this == CLOSED_BY_CACHE;
    }

    public boolean getProofOpen() {
        return this == OPEN;
    }

    public ProofStatus combine(ProofStatus ps) {
        if (getProofOpen() || ps.getProofOpen()) {
            return OPEN;
        } else if (getProofClosedButLemmasLeft() || ps.getProofClosedButLemmasLeft()) {
            return CLOSED_BUT_LEMMAS_LEFT;
        } else {
            return CLOSED;
        }
    }
}
