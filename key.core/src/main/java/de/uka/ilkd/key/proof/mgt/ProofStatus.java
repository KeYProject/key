package de.uka.ilkd.key.proof.mgt;


public enum ProofStatus {
    OPEN, CLOSED_BUT_LEMMAS_LEFT, CLOSED_BY_CACHE, CLOSED;

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
