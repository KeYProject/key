package org.key_project.monkey.product.ui.model;

import org.key_project.util.java.StringUtil;

/**
 * Represents the proof status of a {@link MonKeYProof}.
 * @author Martin Hentschel
 */
public enum MonKeYProofResult {
    /**
     * Proof was not tried.
     */
    UNKNOWN,
    
    /**
     * Proof is still open after automatic try.
     */
    OPEN,
    
    /**
     * Proof is fulfilled after automatic try.
     */
    CLOSED;
    
    /**
     * Returns a human readable text.
     * @return The human readable text.
     */
    public String getDisplayText() {
        switch (this) {
            case OPEN : return "Open";
            case CLOSED : return "Closed";
            default : return StringUtil.EMPTY_STRING;
        }
    }
}
