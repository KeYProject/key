/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.lemma;

import java.util.List;

import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.mgt.ProofEnvironment;
import de.uka.ilkd.key.rule.RewriteTaclet;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.taclettranslation.lemma.ProofObligationCreator;

import org.key_project.logic.Name;
import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableSet;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

/**
 * A taclet created by a {@link LemmaTacletGenerator} together with its soundness proof.
 *
 * <p>
 * The soundness proof obligation is created lazily on first request and in particular
 * <em>not</em> during the rule application that introduces the taclet: proof search must not pay
 * for the proof obligation, and rule applications should not have side effects beyond the proof
 * tree. As long as the soundness proof has not been created (or not been closed), any proof using
 * the taclet is only closed modulo this lemma (see
 * {@link de.uka.ilkd.key.proof.mgt.ProofCorrectnessMgt}).
 */
@NullMarked
public final class GeneratedLemma {

    private final RewriteTaclet taclet;
    private final Proof mainProof;
    private final GeneratedLemmaJustification justification;
    private @Nullable Proof soundnessProof;

    GeneratedLemma(RewriteTaclet taclet, Proof mainProof, Name generatorName) {
        this.taclet = taclet;
        this.mainProof = mainProof;
        this.justification = new GeneratedLemmaJustification(generatorName, this);
    }

    /**
     * returns the justification of the taclet; the identical instance is (re-)registered whenever
     * the lemma is introduced, since pruning removes the justification together with the
     * goal-locally introduced taclet
     */
    public GeneratedLemmaJustification justification() {
        return justification;
    }

    /**
     * returns the generated taclet; within one proof there is exactly one taclet instance per
     * lemma name (see {@link GeneratedLemmaRegistry})
     */
    public RewriteTaclet taclet() {
        return taclet;
    }

    /**
     * returns the soundness proof if it has already been created, and {@code null} otherwise; the
     * proof obligation is not created by this method
     */
    public synchronized @Nullable Proof getSoundnessProofIfPresent() {
        return soundnessProof;
    }

    /**
     * returns the proof for the soundness proof obligation of the taclet, creating (and, if a
     * proof environment is present, registering) it on first call
     */
    public synchronized Proof getOrCreateSoundnessProof() {
        if (soundnessProof == null || soundnessProof.isDisposed()) {
            soundnessProof = createSoundnessProof();
        }
        return soundnessProof;
    }

    /**
     * Creates the soundness proof obligation for the taclet, reusing the standard taclet lemma
     * machinery. The proof runs in a copy of the main proof's initial configuration; the
     * generated taclet itself is not part of that configuration, so it cannot be used to prove
     * itself.
     */
    private Proof createSoundnessProof() {
        final InitConfig poConfig = mainProof.getInitConfig().deepCopy();
        final ImmutableSet<Taclet> tacletsToProve = DefaultImmutableSet.<Taclet>nil().add(taclet);

        final ProofAggregate po = new ProofObligationCreator().create(tacletsToProve,
            new InitConfig[] { poConfig }, DefaultImmutableSet.nil(), List.of());

        final ProofEnvironment env = mainProof.getEnv();
        if (env != null) {
            env.registerProof(new GeneratedLemmaPO(taclet.name(), po), po);
        }
        return po.getFirstProof();
    }
}
