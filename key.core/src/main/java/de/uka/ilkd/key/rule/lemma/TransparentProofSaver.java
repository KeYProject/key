/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.lemma;

import java.nio.file.Path;

import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.io.ProofSaver;
import de.uka.ilkd.key.rule.OneStepSimplifier;
import de.uka.ilkd.key.strategy.StrategyProperties;

import org.jspecify.annotations.NullMarked;

/**
 * Saves a proof in its transparent form: the proof is elaborated onto a fresh proof of the same
 * problem (see {@link LemmaElaboratingProofReplayer}), in which every lemma-eligible one step
 * simplifier application is replaced by the introduction and application of a generated,
 * separately provable taclet, and that proof is saved.
 *
 * <p>
 * The original proof is not modified. The elaborated proof lives in a copy of the original's
 * initial configuration and is disposed after saving.
 */
@NullMarked
public final class TransparentProofSaver {

    /**
     * Statistics of a transparent save.
     *
     * @param elaborated number of simplifier applications replaced by lemma introduction plus
     *        taclet application
     * @param copiedOss number of simplifier applications copied unchanged (not lemma-eligible)
     * @param lemmas number of distinct generated lemmas
     */
    public record Result(int elaborated, int copiedOss, int lemmas) {
    }

    private TransparentProofSaver() {
    }

    /**
     * Elaborates the given proof into its transparent form and saves it to the given file.
     *
     * @param proof the proof to save (left unmodified)
     * @param file the target file
     * @return statistics of the elaboration
     * @throws Exception if the elaboration or saving fails
     */
    public static Result save(Proof proof, Path file) throws Exception {
        final InitConfig config = proof.getInitConfig().deepCopy();
        final Proof target = new Proof(proof.name().toString(), proof.root().sequent(),
            proof.header(), config.createTacletIndex(), config.createBuiltInRuleIndex(), config);
        try {
            // the lemma generator needs an active simplifier on the target proof
            final StrategyProperties sp =
                target.getSettings().getStrategySettings().getActiveStrategyProperties();
            if (StrategyProperties.OSS_OFF
                    .equals(sp.getProperty(StrategyProperties.OSS_OPTIONS_KEY))) {
                sp.setProperty(StrategyProperties.OSS_OPTIONS_KEY, StrategyProperties.OSS_ON);
                target.getSettings().getStrategySettings().setActiveStrategyProperties(sp);
            }
            OneStepSimplifier.refreshOSS(target);

            final LemmaElaboratingProofReplayer replayer =
                LemmaElaboratingProofReplayer.elaborate(proof, target);

            final String error = new ProofSaver(target, file).save();
            if (error != null) {
                throw new IllegalStateException("saving transparent proof failed: " + error);
            }
            return new Result(replayer.getElaboratedCount(), replayer.getCopiedOssCount(),
                GeneratedLemmaRegistry.get(target).getLemmas().size());
        } finally {
            target.dispose();
        }
    }
}
