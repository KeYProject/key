/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic;

import java.nio.file.Files;
import java.nio.file.Path;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.prover.impl.ParallelProver;
import de.uka.ilkd.key.prover.mt.ProofFingerprint;
import de.uka.ilkd.key.util.ProofStarter;

import org.key_project.util.helper.FindResources;

import org.junit.jupiter.api.Assumptions;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.Timeout;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Guards that making the {@link TermFactory} term interner a striped cache did <em>not</em> change
 * the proofs it produces.
 *
 * <p>
 * The interner returns, for a freshly built term, the canonical already-cached instance of an equal
 * term. Striping changes the LRU eviction pattern (per-segment instead of global), so a different
 * set
 * of terms is interned vs. freshly re-created over the course of a proof. Because terms are
 * immutable
 * value objects compared by {@code equals}, that must not affect the proof -- but {@code
 * ServiceCaches} historically warned that "approximate/striped eviction was shown to change
 * proofs",
 * so this is checked rather than assumed: the same obligation is proved single-threaded once with a
 * single global LRU ({@code -Dkey.term.cache.stripes=1}) and once striped ({@code =64}), and the
 * two
 * proofs must be byte-for-byte identical (strict, insertion-order fingerprint -- single-threaded
 * proving is deterministic, so the interner is the only thing that varies between the two runs).
 *
 * @author Claude (KeY multithreading effort)
 */
public class TermCacheProofInvarianceTest {

    @Test
    @Timeout(300)
    void stripedInternerProducesTheSameProofAsAGlobalOne() throws Exception {
        Path examples = FindResources.getExampleDirectory();
        Assumptions.assumeTrue(examples != null, "examples directory not found");

        // Closing, term-heavy proofs that exercise a lot of interning.
        String[] proofs = {
            "standard_key/java_dl/symmArray.key",
            "heap/list/ArrayList_concatenate.key",
            "standard_key/arith/median.key" };

        for (String rel : proofs) {
            Path keyFile = examples.resolve(rel);
            Assumptions.assumeTrue(Files.exists(keyFile), "missing example " + rel);

            ProofFingerprint global = proveSingleThreaded(keyFile, 1);
            ProofFingerprint striped = proveSingleThreaded(keyFile, 64);

            assertEquals(global.orderedDigest, striped.orderedDigest,
                rel + ": the striped term interner produced a different proof than the global one");
            assertEquals(global.closed, striped.closed, rel + ": closed flag differs");
            assertEquals(global.nodeCount, striped.nodeCount, rel + ": node count differs");
        }
    }

    /** Proves the obligation single-threaded with the term cache split into {@code stripes}. */
    private static ProofFingerprint proveSingleThreaded(Path keyFile, int stripes)
            throws Exception {
        String prevStripes = System.getProperty("key.term.cache.stripes");
        String prevParallel = System.getProperty(ParallelProver.PARALLEL_PROPERTY);
        // The stripe count is read when ServiceCaches is constructed, i.e. at load time below.
        System.setProperty("key.term.cache.stripes", Integer.toString(stripes));
        System.setProperty(ParallelProver.PARALLEL_PROPERTY, "false");
        KeYEnvironment<?> env = KeYEnvironment.load(keyFile);
        try {
            Proof proof = env.getLoadedProof();
            ProofStarter starter = new ProofStarter(false);
            starter.init(proof);
            starter.start();
            return ProofFingerprint.of(proof);
        } finally {
            env.dispose();
            restore("key.term.cache.stripes", prevStripes);
            restore(ParallelProver.PARALLEL_PROPERTY, prevParallel);
        }
    }

    private static void restore(String key, String previous) {
        if (previous == null) {
            System.clearProperty(key);
        } else {
            System.setProperty(key, previous);
        }
    }
}
