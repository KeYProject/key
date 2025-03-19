/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.symbolic_execution.strategy.breakpoint;

import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;

/**
 * Provides the basic implementation of an {@link IBreakpoint}.
 *
 * @author Martin Hentschel
 */
public abstract class AbstractBreakpoint implements IBreakpoint {
    /**
     * The proof this stop condition is associated with.
     */
    private final Proof proof;

    /**
     * The flag if the Breakpoint is enabled.
     */
    private boolean enabled;

    /**
     * Constructor.
     *
     * @param proof The {@link Proof} in which this {@link IBreakpoint} is used.
     * @param enabled The enabled state.
     */
    public AbstractBreakpoint(Proof proof, boolean enabled) {
        this.proof = proof;
        this.enabled = enabled;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public void updateState(int maxApplications, long timeout, Proof proof, long startTime,
            int countApplied, Goal goal) {
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean isEnabled() {
        return enabled;
    }

    /**
     * Sets the new enabled value.
     *
     * @param enabled the new value
     */
    public void setEnabled(boolean enabled) {
        this.enabled = enabled;
    }

    /**
     * @return the proof
     */
    public Proof getProof() {
        return proof;
    }
}
