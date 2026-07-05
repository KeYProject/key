/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.lemma;

import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.mgt.RuleJustification;

import org.key_project.logic.Name;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

/**
 * Justification for a taclet created by a {@link LemmaTacletGenerator}: the taclet is a lemma
 * whose validity is established by a dedicated soundness proof, not an axiom and not a consequence
 * of the introducing rule application (which merely computed it).
 */
@NullMarked
public final class GeneratedLemmaJustification implements RuleJustification {

    private final Name generator;
    private final GeneratedLemma lemma;

    public GeneratedLemmaJustification(Name generator, GeneratedLemma lemma) {
        this.generator = generator;
        this.lemma = lemma;
    }

    @Override
    public boolean isAxiomJustification() {
        return false;
    }

    /**
     * returns the name of the generator that created the justified taclet
     */
    public Name getGenerator() {
        return generator;
    }

    /**
     * returns the justified lemma
     */
    public GeneratedLemma getLemma() {
        return lemma;
    }

    /**
     * returns the soundness proof for the justified taclet, or {@code null} if it has not been
     * created yet
     */
    public @Nullable Proof getSoundnessProof() {
        return lemma.getSoundnessProofIfPresent();
    }

    /**
     * returns true iff the soundness proof obligation of the justified taclet has been created
     * and closed (possibly itself depending on further unproven lemmas, which is tracked by
     * {@link de.uka.ilkd.key.proof.mgt.ProofCorrectnessMgt})
     */
    public boolean isProven() {
        return lemma.isProven();
    }

    @Override
    public String toString() {
        final Proof soundnessProof = lemma.getSoundnessProofIfPresent();
        return "generated lemma (by " + generator + ", "
            + (soundnessProof == null ? "soundness proof obligation not yet created"
                    : (soundnessProof.closed() ? "proven" : "soundness proof open"))
            + ")";
    }
}
