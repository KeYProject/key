/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.lemma;

import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.io.ProofSaver;
import de.uka.ilkd.key.taclettranslation.lemma.AutomaticProver;
import de.uka.ilkd.key.util.MiscTools;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * Batch-discharges the soundness proof obligations of generated lemmas: for each lemma it creates
 * (if necessary) the obligation proof and runs automatic proof search with a step bound. Lemmas
 * that close within the bound need no further attention; lemmas that do not are reported back so
 * that they can be shown to the user for manual completion.
 *
 * <p>
 * Closed obligations are certificates and are deliberately not registered in the proof
 * environment, so a batch over many obligations does not flood the environment (and an attached
 * user interface) with closed side proofs; the main proof's status still tracks them through the
 * lemmas. Obligations that remain open are registered (see
 * {@link GeneratedLemma#registerInEnvironment()}) so that an attached user interface surfaces
 * them for manual completion.
 */
@NullMarked
public final class LemmaProver {

    private static final Logger LOGGER = LoggerFactory.getLogger(LemmaProver.class);

    /**
     * Outcome of a batch proving run.
     *
     * @param proven lemmas whose soundness obligation closed within the step bound
     * @param remaining lemmas whose soundness obligation did not close (shown for manual work)
     * @param saved the number of obligation proofs written to disk, or 0 if saving was disabled
     */
    public record Result(List<GeneratedLemma> proven, List<GeneratedLemma> remaining, int saved) {
    }

    private LemmaProver() {
    }

    /**
     * Attempts to discharge the soundness obligations of the given lemmas.
     *
     * @param lemmas the lemmas to prove
     * @param maxSteps the automatic-mode step bound per obligation
     * @param saveDir if non-null, a directory into which every obligation proof is saved
     * @return the outcome
     * @throws Exception if saving a proof fails
     */
    public static Result proveAll(Collection<GeneratedLemma> lemmas, int maxSteps,
            @Nullable Path saveDir) throws Exception {
        final List<GeneratedLemma> proven = new ArrayList<>();
        final List<GeneratedLemma> remaining = new ArrayList<>();
        int saved = 0;

        if (saveDir != null) {
            Files.createDirectories(saveDir);
        }

        for (final GeneratedLemma lemma : lemmas) {
            if (lemma.isProven()) {
                proven.add(lemma);
            } else {
                final Proof po = lemma.getOrCreateSoundnessProof();
                if (!po.closed()) {
                    try {
                        new AutomaticProver().start(po, maxSteps, -1);
                    } catch (InterruptedException e) {
                        Thread.currentThread().interrupt();
                    } catch (RuntimeException e) {
                        // a single obligation whose automatic proof search fails must not abort
                        // the batch; it is reported as remaining for manual inspection
                        LOGGER.warn("automatic proof of lemma {} failed",
                            lemma.taclet().name(), e);
                    }
                }
                if (po.closed()) {
                    // a closed obligation is a certificate; it needs no further attention and is
                    // deliberately not registered in the environment, so a batch that proves many
                    // obligations does not flood the environment (and a user interface) with
                    // closed side proofs. The main proof's status still tracks it through the
                    // lemma. Only obligations that remain open are surfaced for manual work.
                    proven.add(lemma);
                } else {
                    remaining.add(lemma);
                    lemma.registerInEnvironment();
                }

                if (saveDir != null) {
                    final Path file = saveDir.resolve(
                        MiscTools.toValidFileName(lemma.taclet().name().toString()) + ".proof");
                    final String error = new ProofSaver(po, file).save();
                    if (error != null) {
                        throw new IllegalStateException(
                            "saving lemma proof failed: " + error);
                    }
                    saved++;
                }
            }
        }
        return new Result(proven, remaining, saved);
    }
}
