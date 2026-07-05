/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.lemma;

import java.util.List;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.io.OutputStreamProofSaver;
import de.uka.ilkd.key.proof.mgt.ProofEnvironment;
import de.uka.ilkd.key.rule.RewriteTaclet;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.tacletbuilder.RewriteTacletGoalTemplate;
import de.uka.ilkd.key.settings.ProofSettings;
import de.uka.ilkd.key.strategy.StrategyProperties;
import de.uka.ilkd.key.taclettranslation.lemma.ProofObligationCreator;

import org.key_project.logic.Name;
import org.key_project.prover.sequent.Sequent;
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
    private final int aggregatedSteps;
    private @Nullable ProofAggregate soundnessProofAggregate;
    private @Nullable Proof soundnessProof;

    GeneratedLemma(RewriteTaclet taclet, Proof mainProof, Name generatorName,
            int aggregatedSteps) {
        this.taclet = taclet;
        this.mainProof = mainProof;
        this.justification = new GeneratedLemmaJustification(generatorName, this);
        this.aggregatedSteps = aggregatedSteps;
    }

    /**
     * returns the number of base calculus steps the lemma aggregates (display and measurement
     * metadata)
     */
    public int aggregatedSteps() {
        return aggregatedSteps;
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
     * returns the name of the generator that produced this lemma
     */
    public Name generatorName() {
        return justification.getGenerator();
    }

    /**
     * A key identifying this lemma by its content, independent of the introduction point:
     * printed find, assumptions (by polarity), and replacewith. Lemmas with the same content key
     * denote the same simplification and are grouped for display (there may be many, one per
     * introduction point / branch). Note that content-equal lemmas are still distinct taclets
     * with their own soundness obligations, since their proof-local symbols may differ.
     */
    public String contentKey() {
        final Services services = mainProof.getServices();
        final StringBuilder key = new StringBuilder();
        key.append(OutputStreamProofSaver.printTerm(
            LemmaTacletGenerator.removeTermLabels((JTerm) taclet.find(), services), services));
        final Sequent assumes = taclet.assumesSequent();
        for (final var sf : assumes.antecedent()) {
            key.append("\n<= ").append(OutputStreamProofSaver.printTerm(
                LemmaTacletGenerator.removeTermLabels((JTerm) sf.formula(), services),
                services));
        }
        for (final var sf : assumes.succedent()) {
            key.append("\n=> ").append(OutputStreamProofSaver.printTerm(
                LemmaTacletGenerator.removeTermLabels((JTerm) sf.formula(), services),
                services));
        }
        final JTerm rw = (JTerm) ((RewriteTacletGoalTemplate) taclet.goalTemplates().head())
                .replaceWith();
        key.append("\n~> ").append(OutputStreamProofSaver.printTerm(
            LemmaTacletGenerator.removeTermLabels(rw, services), services));
        return key.toString();
    }

    /**
     * returns the soundness proof if it has already been created, and {@code null} otherwise; the
     * proof obligation is not created by this method
     */
    public synchronized @Nullable Proof getSoundnessProofIfPresent() {
        return soundnessProof;
    }

    /**
     * returns true iff the soundness proof obligation has been created and is not disposed
     */
    public synchronized boolean isSoundnessProofPresent() {
        return soundnessProof != null && !soundnessProof.isDisposed();
    }

    /**
     * returns true iff the soundness proof obligation has been created and closed
     */
    public synchronized boolean isProven() {
        return isSoundnessProofPresent() && soundnessProof.closed();
    }

    /**
     * returns the proof for the soundness proof obligation of the taclet, creating (and, if a
     * proof environment is present, registering) it on first call
     */
    public synchronized Proof getOrCreateSoundnessProof() {
        return getOrCreateSoundnessProofAggregate().getFirstProof();
    }

    /**
     * returns the proof aggregate for the soundness proof obligation of the taclet, creating
     * (and, if a proof environment is present, registering in it) it on first call. The
     * aggregate is what a user interface registers to display and drive the proof.
     */
    public synchronized ProofAggregate getOrCreateSoundnessProofAggregate() {
        if (soundnessProof == null || soundnessProof.isDisposed()) {
            soundnessProofAggregate = createSoundnessProof();
            soundnessProof = soundnessProofAggregate.getFirstProof();
        }
        return soundnessProofAggregate;
    }

    /**
     * Creates the soundness proof obligation for the taclet, reusing the standard taclet lemma
     * machinery. The proof runs in a copy of the main proof's initial configuration; the
     * generated taclet itself is not part of that configuration, so it cannot be used to prove
     * itself.
     */
    private ProofAggregate createSoundnessProof() {
        final InitConfig poConfig = mainProof.getInitConfig().deepCopy();
        // The soundness of a generated lemma must be established in the base calculus, using the
        // individual rewrite rules the lemma aggregates. The one step simplifier is switched off
        // entirely for the obligation: not only its transparent mode (which would discharge the
        // obligation by generating and applying further lemmas — re-doing the very simplification
        // it must justify, a circular and non-terminating justification), but also its opaque
        // mode, which performs the same aggregated simplification in one hidden step and would
        // therefore close the obligation by exactly the transformation under scrutiny.
        disableOneStepSimplification(poConfig);
        final ImmutableSet<Taclet> tacletsToProve = DefaultImmutableSet.<Taclet>nil().add(taclet);

        final ProofAggregate po = new ProofObligationCreator().create(tacletsToProve,
            new InitConfig[] { poConfig }, DefaultImmutableSet.nil(), List.of());

        final ProofEnvironment env = mainProof.getEnv();
        if (env != null) {
            env.registerProof(new GeneratedLemmaPO(taclet.name(), po), po);
        }
        return po;
    }

    /**
     * Switches the one step simplifier off in the given configuration, so that the soundness
     * proof is conducted in the base calculus (see {@link #createSoundnessProof()}).
     */
    private static void disableOneStepSimplification(InitConfig config) {
        final ProofSettings settings = config.getSettings();
        if (settings == null) {
            return;
        }
        final StrategyProperties sp =
            settings.getStrategySettings().getActiveStrategyProperties();
        sp.setProperty(StrategyProperties.OSS_OPTIONS_KEY, StrategyProperties.OSS_OFF);
        settings.getStrategySettings().setActiveStrategyProperties(sp);
    }
}
