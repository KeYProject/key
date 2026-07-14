/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof.mgt;

public interface RuleJustification {

    boolean isAxiomJustification();

    /**
     * Returns true iff this justification is local to the proof it was created in, e.g. because
     * it refers to the proof node that introduced the justified rule. Proof-local justifications
     * are not carried over when an initial configuration is copied for another proof: they would
     * reference foreign proof nodes there, and the stale entries would collide with the rule
     * (re-)introductions of the new proof (dynamically introduced rules such as {@code \addrule}
     * taclets or generated lemmas register their justification when they are introduced).
     *
     * @return true iff this justification must not survive an initial-configuration copy
     */
    default boolean isProofLocal() {
        return false;
    }
}
